import Mathlib

open Set

namespace MyArzelaAscoli

/-!
# Arzelà–Ascoli theorem

`BoundedContinuousFunction X Y` is the space of bounded continuous
functions from `X` to `Y`, equipped with the uniform convergence
topology.

When `X` is compact, every continuous function from `X` into a metric
space is bounded.
-/

variable {X Y : Type*}
variable [TopologicalSpace X] [CompactSpace X]
variable [MetricSpace Y]

/--
Arzelà–Ascoli: an equicontinuous family whose values all lie in a
fixed compact subset of `Y` has compact closure.

The compact set `K` is common to every function and every point.
-/
theorem compact_closure_of_equicontinuous
    (F : Set (BoundedContinuousFunction X Y))
    (K : Set Y)
    (hK : IsCompact K)
    (hvalues :
      ∀ (f : BoundedContinuousFunction X Y) (x : X),
        f ∈ F → f x ∈ K)
    (hequi :
      Equicontinuous (fun f : F => (f.1 : X → Y))) :
    IsCompact (closure F) := by
  exact
    BoundedContinuousFunction.arzela_ascoli
      K hK F hvalues hequi

/--
If the family is closed, then the family itself is compact.
-/
theorem compact_of_closed_of_equicontinuous
    (F : Set (BoundedContinuousFunction X Y))
    (K : Set Y)
    (hK : IsCompact K)
    (hclosed : IsClosed F)
    (hvalues :
      ∀ (f : BoundedContinuousFunction X Y) (x : X),
        f ∈ F → f x ∈ K)
    (hequi :
      Equicontinuous (fun f : F => (f.1 : X → Y))) :
    IsCompact F := by
  exact
    BoundedContinuousFunction.arzela_ascoli₂
      K hK F hclosed hvalues hequi

/--
Real-valued version.

If an equicontinuous family is uniformly bounded by `M`, its closure
is compact in the topology of uniform convergence.
-/
theorem real_compact_closure_of_uniformly_bounded
    (F : Set (BoundedContinuousFunction X ℝ))
    (M : ℝ)
    (hbound :
      ∀ f ∈ F, ∀ x : X, |f x| ≤ M)
    (hequi :
      Equicontinuous (fun f : F => (f.1 : X → ℝ))) :
    IsCompact (closure F) := by
  -- All function values lie in the compact interval [-M, M].
  apply compact_closure_of_equicontinuous
    F (Set.Icc (-M) M) isCompact_Icc
  · intro f x hf
    exact abs_le.mp (hbound f hf x)
  · exact hequi

end MyArzelaAscoli

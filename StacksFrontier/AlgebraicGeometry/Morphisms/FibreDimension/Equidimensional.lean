module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Comparison
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Components
public import StacksFrontier.Topology.Dimension.Equidimensional
public import Mathlib.Tactic.CrossRefAttribute

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Equidimensional fibres and relative dimension

A scheme locally of finite type over a field is equidimensional of dimension `d` exactly when its
local dimension is `d` at every point: the local dimension at a point is the largest dimension of
an irreducible component through that point (Tag 0A21), so constancy of the local dimension and
equality of the dimensions of all the components determine each other.

This gives the two stability properties of the relative dimension of Tag 02NJ used when a
morphism is cut down to an open subscheme of its source or factored through an open subscheme of
its target: the fibres only get replaced by open subspaces, respectively by homeomorphic copies.

## Main results

* `AlgebraicGeometry.topologicalKrullDimAt_eq_of_equidimensional` and
  `AlgebraicGeometry.equidimensional_of_topologicalKrullDimAt_eq` are the two directions of the
  comparison for a scheme locally of finite type over a field.
* `AlgebraicGeometry.topologicalKrullDimAt_fiber_eq_of_relativeDimension`: on an open subscheme
  of constant relative dimension `d` the fibre has local dimension `d`.
* `AlgebraicGeometry.RelativeDimension.comp_isOpenImmersion` and
  `AlgebraicGeometry.RelativeDimension.of_comp_isOpenImmersion`: relative dimension is inherited
  by the restriction of the source to an open subscheme and by a factorization through an open
  subscheme of the target.
* `AlgebraicGeometry.topologicalKrullDim_eq_of_relativeDimension`: over a one-point base the
  relative dimension of a morphism out of a nonempty scheme is the dimension of its source.

## References

* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
* [Stacks Project, Tag 02NJ](https://stacks.math.columbia.edu/tag/02NJ)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- If `f` has relative dimension `d`, the fibre through any point `x` of the source has local
dimension `d` at `x`. -/
private theorem topologicalKrullDimAt_fiber_eq_of_relativeDimension_aux {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] {d : ℕ} (hf : RelativeDimension f d) (x : X) :
    stacksTopologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = (d : WithBot ℕ∞) := by
  have : LocallyOfFiniteType (f.fiberToSpecResidueField (f x)) := by
    change LocallyOfFiniteType (Limits.pullback.snd f (S.fromSpecResidueField (f x)))
    infer_instance
  obtain ⟨heq, hdim⟩ := hf (f x) ⟨f.asFiber x⟩
  exact topologicalKrullDimAt_eq_of_equidimensional (S.residueField (f x)) (f.fiber (f x))
    (f.fiberToSpecResidueField (f x)) heq hdim (f.asFiber x)

/-- On an open subscheme over which a morphism has relative dimension `d`, the fibre has local
dimension exactly `d` at every point. -/
public theorem topologicalKrullDimAt_fiber_eq_of_relativeDimension {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] (U : X.Opens) (d : ℕ)
    (hU : RelativeDimension (U.ι ≫ f) d) (x : X) (hx : x ∈ U) :
    stacksTopologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = (d : WithBot ℕ∞) := by
  exact (fiberDimensionAt_comp_openImmersion U.ι f ⟨x, hx⟩).symm.trans
    (topologicalKrullDimAt_fiber_eq_of_relativeDimension_aux (U.ι ≫ f) hU ⟨x, hx⟩)

end AlgebraicGeometry

end

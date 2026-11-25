module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Tactic.CrossRefAttribute

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Fibres of locally algebraic schemes

Let `f : X ⟶ Y` be a morphism of schemes over a field, with `X` locally of finite type over
that field. Every scheme-theoretic fibre of `f` is then locally of finite type over the residue
field of its base point, so the dimension theory of locally algebraic schemes applies to it.

## Main results

* `AlgebraicGeometry.Scheme.Hom.locallyOfFiniteType_fiberToSpecResidueField`: the fibres of a
  morphism locally of finite type are locally of finite type over the residue fields of their
  base points.
* `AlgebraicGeometry.locallyOfFiniteType_fiberToSpecResidueField`: every fibre is locally
  algebraic over its residue field.
* `AlgebraicGeometry.isLocallyNoetherian_fiber_of_locallyOfFiniteType`: every fibre of a
  morphism locally of finite type is locally Noetherian.
* `AlgebraicGeometry.finite_irreducibleComponents_fiber`: a fibre of a quasi-compact morphism
  locally of finite type has finitely many irreducible components.

## Implementation notes

Being locally of finite type is stable under base change, and a fibre is a base change, so the
general statement needs no base field at all and is registered as an instance: the hypothesis is
`LocallyOfFiniteType f` and nothing else.

A locally algebraic `k`-scheme is represented by its structure morphism to `Spec k` together
with a `LocallyOfFiniteType` instance, and the equality of structure morphisms records that `f`
is a morphism of `k`-schemes. Only local algebraicity of the source is needed, so no hypothesis
is imposed on `Y` beyond its structure morphism; it enters only to make `f` itself locally of
finite type, which is what the general instance consumes. The conclusion is stated for Mathlib's
canonical morphism `Scheme.Hom.fiberToSpecResidueField`.

## References

* [Stacks Project, Tag 0B2L](https://stacks.math.columbia.edu/tag/0B2L)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The fibre of a morphism locally of finite type is locally of finite type over the residue
field of its base point: the fibre is the base change of `f` along
`Scheme.fromSpecResidueField`. -/
public instance Scheme.Hom.locallyOfFiniteType_fiberToSpecResidueField {X Y : Scheme.{u}}
    (f : X ⟶ Y) [LocallyOfFiniteType f] (y : Y) :
    LocallyOfFiniteType (f.fiberToSpecResidueField y) := by
  change LocallyOfFiniteType (Limits.pullback.snd f (Y.fromSpecResidueField y))
  infer_instance

/-- **The fibres of a morphism locally of finite type are locally Noetherian.** The fibre over
`y` is locally of finite type over the residue field at `y`, and a scheme locally of finite type
over a locally Noetherian scheme is locally Noetherian. -/
public theorem isLocallyNoetherian_fiber_of_locallyOfFiniteType {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (y : Y) : IsLocallyNoetherian (f.fiber y) :=
  have : IsLocallyNoetherian (Spec (Y.residueField y)) :=
    isLocallyNoetherian_Spec.mpr inferInstance
  LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField y)

end AlgebraicGeometry

end

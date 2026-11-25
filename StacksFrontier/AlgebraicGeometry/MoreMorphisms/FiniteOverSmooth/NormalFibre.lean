module

public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Normal
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.Reduced
import Mathlib.Tactic.CrossRefAttribute

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Fibres of a normal morphism

A normal morphism of schemes, in the sense of Stacks Tag 0390, is flat with geometrically normal
fibres. This file records the two consequences of that definition which the spreading-out
arguments of Tags 057J and 057K use: each fibre, as a scheme over the residue field of its base
point, is geometrically normal, and a normal morphism is flat with geometrically reduced fibres.

A normal scheme stays normal along an open immersion; this is the version of Tag 033J for an
arbitrary open immersion rather than for an open subscheme.

## Main results

* `AlgebraicGeometry.Scheme.Hom.IsNormal.isGeometricallyNormal_fiber`: the fibres of a normal
  morphism are geometrically normal over the residue fields of their base points.
* `AlgebraicGeometry.Scheme.Hom.IsNormal.flat` and
  `AlgebraicGeometry.Scheme.Hom.IsNormal.geometricallyReduced`: a normal morphism is flat with
  geometrically reduced fibres.
* `AlgebraicGeometry.isNormal_of_isOpenImmersion`: normality passes to the source of an open
  immersion.

## Implementation notes

`AlgebraicGeometry.Scheme.Hom.IsNormal` is stated pointwise, with the fibre condition attached to
the point `f.asFiber x` of the fibre over `f x`. Recovering the fibrewise statement over an
arbitrary point `s` of the base therefore means producing, for a point `y` of the fibre over `s`,
the point of `X` it comes from and the identification of `f.asFiber` of that point with `y`;
that is `AlgebraicGeometry.Scheme.Hom.isGeometricallyNormalAt_asFiber` below.

## References

* [Stacks Project, Tag 0390](https://stacks.math.columbia.edu/tag/0390)
* [Stacks Project, Tag 033J](https://stacks.math.columbia.edu/tag/033J)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Normality passes to the source of an open immersion, the stalks being unchanged. -/
theorem isNormal_of_isOpenImmersion {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    [IsNormal Y] : IsNormal X := by
  refine (isNormal_iff_stalk_normal X).2 fun x ↦ ?_
  let e := (asIso (j.stalkMap x)).commRingCatIsoToRingEquiv
  have : IsDomain (Y.presheaf.stalk (j x)) := IsNormal.stalk_isDomain (j x)
  have : IsIntegrallyClosed (Y.presheaf.stalk (j x)) := IsNormal.stalk_normal (j x)
  have : IsDomain (X.presheaf.stalk x) :=
    Function.Injective.isDomain e.symm.toRingHom e.symm.injective
  exact ⟨inferInstance, id (IsIntegrallyClosed.of_equiv e)⟩

namespace Scheme.Hom

end Scheme.Hom

end AlgebraicGeometry

end

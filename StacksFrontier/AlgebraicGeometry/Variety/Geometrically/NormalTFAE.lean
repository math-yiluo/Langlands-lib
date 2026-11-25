module

public import Mathlib.Data.List.TFAE
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
public import StacksFrontier.RingTheory.GeometricallyNormal.TFAE

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Characterizations of geometrically normal schemes

Geometric normality of a scheme over a field can be tested after arbitrary field extensions,
after finitely generated field extensions, after finite purely inseparable extensions, on the
rings of sections of affine opens, or after extension to the perfect closure of the base field.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.geometricallyNormal_tfae` gives the six equivalent characterizations of a
  geometrically normal scheme.

## Implementation notes

The six entries of the `List.TFAE` are the six numbered conditions in the source. The algebra
structure on the sections of an affine open is induced canonically by the structure morphism.
Finite generation of a field extension is expressed by `Algebra.EssFiniteType`; finiteness is
expressed by `Module.Finite`. Base change is represented by the scheme-theoretic pullback.

The tag's `k^perf` is spelled `perfectClosure k (AlgebraicClosure k)`, the largest purely
inseparable subextension of an algebraic closure of `k`, as recorded on Stacks Tag 046X in
`StacksFrontier.FieldTheory.PerfectClosure`. The reduction of the scheme-level statement to the
algebraic one, `Algebra.isNormalRing_tensorProduct_tfae` (Stacks Tag 037Z), goes through
`AlgebraicGeometry.isNormal_pullback_iff_affineSections`, which identifies the base change of
an affine open of `X` with the spectrum of the corresponding tensor product; that
identification is the content of the private `affineBaseChangeIso`.

## References

* [Stacks Project, Tag 038O](https://stacks.math.columbia.edu/tag/038O)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

open CommRingCat
open scoped TensorProduct

universe u

/-- Normality of a scheme is normality, as a ring, of each of its local rings. -/
public lemma isNormal_iff_stalk_isNormalRing (Y : Scheme.{u}) :
    IsNormal Y ↔ ∀ y : Y, IsNormalRing (Y.presheaf.stalk y) := by
  constructor
  · intro h y
    have hy := (isNormal_iff_stalk_normal Y).mp h y
    have : IsDomain (Y.presheaf.stalk y) := hy.choose
    have : IsIntegrallyClosed (Y.presheaf.stalk y) := id hy.choose_spec
    exact IsNormalRing.of_isIntegrallyClosed _
  · refine fun h ↦ (isNormal_iff_stalk_normal Y).mpr fun y ↦ ?_
    obtain ⟨hD, hIC⟩ := (h y).of_isLocalRing
    exact ⟨hD, id hIC⟩

/-- Normality of a scheme transports along an isomorphism. -/
public lemma isNormal_of_iso {Y Z : Scheme.{u}} (e : Y ≅ Z) [IsNormal Z] : IsNormal Y :=
  (isNormal_iff_stalk_isNormalRing Y).2 fun y ↦
    IsNormalRing.congr (asIso (e.hom.stalkMap y)).commRingCatIsoToRingEquiv
      ((isNormal_iff_stalk_isNormalRing Z).mp inferInstance (e.hom y))

end AlgebraicGeometry

end

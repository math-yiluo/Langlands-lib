/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLineNormalization
public import WeilConjectures.EtaleCohomology.TateTwist.KummerClass
public import WeilConjectures.EtaleCohomology.TateTwist.AffineLineDescentClauses
public import WeilConjectures.SixFunctors.Etale.Derived.DirectImageAmplitude

/-!
# The cohomology of `𝔸¹` and `𝔾ₘ` with coefficients in the Tate twist `μₙ ⊗ Λ`

For the concrete Tate twist `Λ(1) = μₙ ⊗ Λ` and its Kummer classes
(`AlgebraicGeometry.Etale.hasKummerClass`), the computations of `sk-prop-a1-kummer` on the
affine line `p : 𝔸¹_B ⟶ B` and on `π : 𝔾_{m,B} ⟶ 𝔸¹_B ⟶ B`, over a base `B` separated and
locally of finite type over a field on which `n` is invertible:

* `Rp_* Λ(1)` is `Λ_B(1)` in degree zero;
* restriction along `j : 𝔾_{m,B} ⟶ 𝔸¹_B` identifies `R⁰p_* Λ(1)` with `R⁰π_* Λ(1)`;
* `R¹π_* Λ(1)` is free of rank one on the Kummer class `κ(t)` of the coordinate;
* `R^mπ_* Λ(1) = 0` for `m ≥ 2`.

These are the clauses (a)–(c) of `sk-prop-a1-kummer`, read for the twisted coefficients `Λ(1)`
as they are used in the proof of `sk-prop-a1`, and with the generator `κ(t)` of clause (b) made
explicit. The forms `AlgebraicGeometry.Etale.nonempty_iso_homology_one_multiplicativeGroup` and
`AlgebraicGeometry.Etale.isZero_homology_multiplicativeGroup` of
`WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine` assume a normalized twist datum,
which for the concrete twist is the very statement `sk-prop-a1` they are used to prove, and they
do not name the generator; hence these statements for the concrete twist. The vanishing in
negative degrees is the left t-exactness of the direct images.

Over an algebraically closed field and for `B` quasi-compact, the same computations, phrased
for the direct image along the composite `G ⟶ 𝔸¹_B ⟶ B` of an arbitrary open complement of the
zero section, are proved in `WeilConjectures.EtaleCohomology.Purity.Smooth.GmRelativeKummer`,
for instance clause (c) as
`AlgebraicGeometry.Etale.isZero_homology_rightDerivedLowerStar_tateObject_multiplicativeGroup`;
the statements here are over an arbitrary field.

## Main statements

- `AlgebraicGeometry.Etale.affineLine_multiplicativeGroup_homology_tateObject`
- `AlgebraicGeometry.Etale.isZero_homology_rightDerivedLowerStar_tateObject_affineLine`
- `AlgebraicGeometry.Etale.isIso_homology_zero_map_unit_multiplicativeGroup`
- `AlgebraicGeometry.Etale.isIso_shiftMap_kummerClassAffineLineDirectImage`
- `AlgebraicGeometry.Etale.isZero_homology_rightDerivedLowerStar_tateObject_basicOpen`
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [NeZero (ringChar Λ)]
  {k : Type u} [Field k] (B : Scheme.{u}) (aB : B ⟶ Spec (.of k)) [IsSeparated aB]
  [LocallyOfFiniteType aB] [HasInvertibleExponent Λ B]

attribute [local instance] HasInvertibleExponent.opens

include aB in
/-- Blueprint `sk-prop-a1-kummer`: The affine line and `𝔾ₘ` with `Λ(1)`-coefficients

The proposition `sk-prop-a1-kummer`, clauses (a)–(c), for the concrete Tate twist
`Λ(1) = μₙ ⊗ Λ`, with the generator `κ(t)` of clause (b) made explicit. Write
`p : 𝔸¹_B ⟶ B` for the projection, `j : 𝔾_{m,B} ⟶ 𝔸¹_B` for the open complement of the zero
section and `π = p ∘ j`, so that `Rπ_* Λ(1) = Rp_* Rj_* j^* Λ(1)`:
* (a) `R^m p_* Λ(1) = 0` for `m > 0` (the affine line is acyclic, and `Λ(1)` is pulled back
  from `B`);
* (b) restriction along `j` identifies `R⁰p_* Λ(1)` with `R⁰π_* Λ(1)`, and the Kummer class
  `κ(t) : Λ_B ⟶ (Rπ_* Λ(1))[1]` (`AlgebraicGeometry.Etale.kummerClassAffineLineDirectImage`)
  induces an isomorphism `Λ_B ≅ R¹π_* Λ(1)`;
* (c) `R^m π_* Λ(1) = 0` for `m ≥ 2`.

The forms of this proposition in `WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine`
assume a normalized twist datum, which for the concrete twist is the statement `sk-prop-a1`
proved from this one, and do not name the generator. -/
theorem affineLine_multiplicativeGroup_homology_tateObject :
    (∀ n : ℤ, 0 < n → IsZero ((_root_.DerivedCategory.homologyFunctor _ n).obj
      ((R((𝔸(ULift.{u} (Fin 1); B) ↘ B)_*[ModuleCat.{u + 1} Λ])).obj
        (tateObject Λ 𝔸(ULift.{u} (Fin 1); B) 1)))) ∧
    IsIso ((_root_.DerivedCategory.homologyFunctor _ 0).map
      ((R((𝔸(ULift.{u} (Fin 1); B) ↘ B)_*[ModuleCat.{u + 1} Λ])).map
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
          ((𝔸(ULift.{u} (Fin 1); B).basicOpen (AffineSpace.coord B (ULift.up 0))).ι)).unit.app
            (tateObject Λ 𝔸(ULift.{u} (Fin 1); B) 1)))) ∧
    IsIso ((_root_.DerivedCategory.homologyFunctor _ 0).shiftMap
      (kummerClassAffineLineDirectImage Λ B) 0 1 (by norm_num)) ∧
    (∀ n : ℤ, 2 ≤ n → IsZero ((_root_.DerivedCategory.homologyFunctor _ n).obj
      ((R((𝔸(ULift.{u} (Fin 1); B) ↘ B)_*[ModuleCat.{u + 1} Λ])).obj
        ((R(((𝔸(ULift.{u} (Fin 1); B).basicOpen (AffineSpace.coord B (ULift.up 0))).ι)_*[
            ModuleCat.{u + 1} Λ])).obj
          ((L(((𝔸(ULift.{u} (Fin 1); B).basicOpen (AffineSpace.coord B (ULift.up 0))).ι)^*[
            ModuleCat.{u + 1} Λ])).obj (tateObject Λ 𝔸(ULift.{u} (Fin 1); B) 1)))))) :=
  ⟨isZero_homology_rightDerivedLowerStar_tateObject_affineLine_of_field Λ B aB,
    isIso_homology_zero_map_unit_multiplicativeGroup_of_field Λ B aB,
    isIso_shiftMap_kummerClassAffineLineDirectImage_of_field Λ B aB,
    isZero_homology_rightDerivedLowerStar_tateObject_basicOpen_of_field Λ B aB⟩

include aB in
/-- Blueprint `sk-prop-a1-kummer`: The affine line and `𝔾ₘ` with `Λ(1)`-coefficients

*(a), twisted.* For the projection `p : 𝔸¹_B ⟶ B`, `R^m p_* Λ(1) = 0` for `m > 0`: the affine
line is acyclic, and `Λ(1)` is pulled back from `B`, so by the projection formula the twisted
statement follows from `Rp_* Λ ≅ Λ_B`. -/
theorem isZero_homology_rightDerivedLowerStar_tateObject_affineLine_of_pos (n : ℤ) (hn : 0 < n) :
    IsZero ((_root_.DerivedCategory.homologyFunctor _ n).obj
      ((R((𝔸(ULift.{u} (Fin 1); B) ↘ B)_*[ModuleCat.{u + 1} Λ])).obj
        (tateObject Λ 𝔸(ULift.{u} (Fin 1); B) 1))) :=
  (affineLine_multiplicativeGroup_homology_tateObject Λ B aB).1 n hn

include aB in
/-- Blueprint `sk-prop-a1-kummer`: The affine line and `𝔾ₘ` with `Λ(1)`-coefficients

*(b), degree zero.* For the open complement `j : 𝔾_{m,B} ⟶ 𝔸¹_B` of the zero section, the
restriction `R⁰p_* Λ(1) ⟶ R⁰π_* Λ(1)` is an isomorphism (`p^*` is an isomorphism onto
`R⁰π_* Λ(1) ≅ Λ_B(1)`). -/
theorem isIso_homology_zero_map_unit_multiplicativeGroup :
    IsIso ((_root_.DerivedCategory.homologyFunctor _ 0).map
      ((R((𝔸(ULift.{u} (Fin 1); B) ↘ B)_*[ModuleCat.{u + 1} Λ])).map
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
          ((𝔸(ULift.{u} (Fin 1); B).basicOpen (AffineSpace.coord B (ULift.up 0))).ι)).unit.app
            (tateObject Λ 𝔸(ULift.{u} (Fin 1); B) 1)))) :=
  (affineLine_multiplicativeGroup_homology_tateObject Λ B aB).2.1

include aB in
/-- Blueprint `sk-prop-a1-kummer`: The affine line and `𝔾ₘ` with `Λ(1)`-coefficients

*(b), degree one: the Kummer generator.* `R¹π_* Λ(1)` is free of rank one on the Kummer class
`κ(t)` of the coordinate: the section `κ(t) : Λ_B ⟶ (Rπ_* Λ(1))[1]`
(`AlgebraicGeometry.Etale.kummerClassAffineLineDirectImage`) induces an isomorphism
`Λ_B ≅ R¹π_* Λ(1)`, `1 ↦ κ(t)`. -/
theorem isIso_shiftMap_kummerClassAffineLineDirectImage :
    IsIso ((_root_.DerivedCategory.homologyFunctor _ 0).shiftMap
      (kummerClassAffineLineDirectImage Λ B) 0 1 (by norm_num)) :=
  (affineLine_multiplicativeGroup_homology_tateObject Λ B aB).2.2.1

include aB in
/-- Blueprint `sk-prop-a1-kummer`: The affine line and `𝔾ₘ` with `Λ(1)`-coefficients

*(c).* `R^m π_* Λ(1) = 0` for `m ≥ 2`, by the cohomological dimension of affine curves over an
algebraically closed field. -/
theorem isZero_homology_rightDerivedLowerStar_tateObject_basicOpen_of_two_le
    (n : ℤ) (hn : 2 ≤ n) :
    IsZero ((_root_.DerivedCategory.homologyFunctor _ n).obj
      ((R((𝔸(ULift.{u} (Fin 1); B) ↘ B)_*[ModuleCat.{u + 1} Λ])).obj
        ((R(((𝔸(ULift.{u} (Fin 1); B).basicOpen (AffineSpace.coord B (ULift.up 0))).ι)_*[
            ModuleCat.{u + 1} Λ])).obj
          ((L(((𝔸(ULift.{u} (Fin 1); B).basicOpen (AffineSpace.coord B (ULift.up 0))).ι)^*[
            ModuleCat.{u + 1} Λ])).obj (tateObject Λ 𝔸(ULift.{u} (Fin 1); B) 1))))) :=
  (affineLine_multiplicativeGroup_homology_tateObject Λ B aB).2.2.2 n hn

omit [Finite Λ] in
/-- The Tate twist `Λ_X(m)` is concentrated in degree zero, so it lies in `D^{≥ 0}`. -/
instance isGE_tateObject (X : Scheme.{u}) [HasInvertibleExponent Λ X] (m : ℤ) :
    (tateObject Λ X m).IsGE 0 :=
  DerivedCategory.TStructure.t.isGE_of_iso (tateTwistObjectIsoSingleFunctor Λ X m).symm 0

include aB in
/-- Blueprint `sk-prop-a1-kummer`: The affine line and `𝔾ₘ` with `Λ(1)`-coefficients

`Rp_* Λ(1)` has cohomology only in degree zero. -/
theorem isZero_homology_rightDerivedLowerStar_tateObject_affineLine (n : ℤ) (hn : n ≠ 0) :
    IsZero ((_root_.DerivedCategory.homologyFunctor _ n).obj
      ((R((𝔸(ULift.{u} (Fin 1); B) ↘ B)_*[ModuleCat.{u + 1} Λ])).obj
        (tateObject Λ 𝔸(ULift.{u} (Fin 1); B) 1))) := by
  rcases lt_or_gt_of_ne hn with hn | hn
  · have := isGE_rightDerivedLowerStar_obj Λ (𝔸(ULift.{u} (Fin 1); B) ↘ B)
      (tateObject Λ 𝔸(ULift.{u} (Fin 1); B) 1) 0
    exact _root_.DerivedCategory.isZero_of_isGE _ 0 n hn
  · exact isZero_homology_rightDerivedLowerStar_tateObject_affineLine_of_pos Λ B aB n hn

include aB in
/-- Blueprint `sk-prop-a1-kummer`: The affine line and `𝔾ₘ` with `Λ(1)`-coefficients

`Rπ_* Λ(1)` has cohomology only in degrees zero and one. -/
theorem isZero_homology_rightDerivedLowerStar_tateObject_basicOpen (n : ℤ)
    (hn₀ : n ≠ 0) (hn₁ : n ≠ 1) :
    IsZero ((_root_.DerivedCategory.homologyFunctor _ n).obj
      ((R((𝔸(ULift.{u} (Fin 1); B) ↘ B)_*[ModuleCat.{u + 1} Λ])).obj
        ((R(((𝔸(ULift.{u} (Fin 1); B).basicOpen (AffineSpace.coord B (ULift.up 0))).ι)_*[
            ModuleCat.{u + 1} Λ])).obj
          ((L(((𝔸(ULift.{u} (Fin 1); B).basicOpen (AffineSpace.coord B (ULift.up 0))).ι)^*[
            ModuleCat.{u + 1} Λ])).obj (tateObject Λ 𝔸(ULift.{u} (Fin 1); B) 1))))) := by
  rcases lt_or_gt_of_ne hn₀ with hn | hn
  · let j := (𝔸(ULift.{u} (Fin 1); B).basicOpen (AffineSpace.coord B (ULift.up.{u} (0 : Fin 1)))).ι
    have : ((L((j)^*[ModuleCat.{u + 1} Λ])).obj (tateObject Λ 𝔸(ULift.{u} (Fin 1); B) 1)).IsGE 0 :=
      DerivedCategory.TStructure.t.isGE_of_iso (leftDerivedUpperStarTateObjectIso j 1).symm 0
    have := isGE_rightDerivedLowerStar_obj Λ j
      ((L((j)^*[ModuleCat.{u + 1} Λ])).obj (tateObject Λ 𝔸(ULift.{u} (Fin 1); B) 1)) 0
    have := isGE_rightDerivedLowerStar_obj Λ (𝔸(ULift.{u} (Fin 1); B) ↘ B)
      ((R((j)_*[ModuleCat.{u + 1} Λ])).obj
        ((L((j)^*[ModuleCat.{u + 1} Λ])).obj (tateObject Λ 𝔸(ULift.{u} (Fin 1); B) 1))) 0
    exact _root_.DerivedCategory.isZero_of_isGE _ 0 n hn
  · exact isZero_homology_rightDerivedLowerStar_tateObject_basicOpen_of_two_le
      Λ B aB n (by lia)

end Etale

end AlgebraicGeometry

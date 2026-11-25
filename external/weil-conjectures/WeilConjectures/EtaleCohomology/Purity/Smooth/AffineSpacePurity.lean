/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.AffineSpaceTwistAdjunction

/-!
# Affine-space purity: the `Rp^!`-form

Let `Y` be a separated scheme of finite type over a field on which the exponent of the finite
coefficient ring `Λ` is invertible, and `p_d : 𝔸^d_Y → Y` the projection. This file proves
clause (ii) of blueprint `proposition-purity-vector-bundles`, `Rp_d^! K ≅ Lp_d^* K (d)[2d]` for
`K ∈ D^b_{ctf}(Y, Λ)`.

Affine-line purity is read off from the affine-space ambient adjunction
`Rp_! ⊣ p^*(1)[2]` (`lemma-affine-space-etale-localization--1`,
`AlgebraicGeometry.Etale.nonempty_rightDerivedLowerShriek_adjunction_affineSpace`), and the
general case iterates it through `𝔸^{d+1}_Y = 𝔸¹_{𝔸^d_Y}`
(`AlgebraicGeometry.AffineSpace.sumIso`).

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_affineLine`: affine-line purity,
  `Rp^! K ≅ Lp^* K (1)[2]`.
- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_affineSpace`: clause (ii),
  affine-space purity `Rp_c^! K ≅ Lp_c^* K (c)[2c]`.
- `AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_affineSpace`: its case `K = Λ_B`,
  `ω_{p_c} ≅ Λ(c)[2c]`.
- `AlgebraicGeometry.Etale.nonempty_iso_sectionInvariant_affineSpace`: the section invariant of
  the standard pair, `𝒞(𝔸^c_B → B, 0) ≅ Λ_B(c)[2c]`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ]

/-! ### The `Rp^!`-form -/

/-- Blueprint `lemma-affine-space-etale-localization--1`: affine-line purity

For the projection `p : 𝔸¹_Y → Y` of the affine line over a separated scheme of finite type
over a field, on which the exponent of `Λ` is invertible, and `K ∈ D^b_{ctf}(Y, Λ)`,

`Rp^! K ≅ Lp^* K (1)[2]`.

In the blueprint the isomorphism is the comparison `γ_{p,K}`, the transpose under
`Rp_! ⊣ Rp^!` of the integration map built from the projective-line trace
(`definition-trace-map-affine-line`); this comparison is not constructed, so only the
existence of the isomorphism is recorded.

The proof follows the blueprint: `Rp^!` is by definition the right adjoint of `Rp_!`, and
`Rp_! ⊣ p^*(1)[2]` is the affine-space ambient adjunction
(`AlgebraicGeometry.Etale.nonempty_rightDerivedLowerShriek_adjunction_affineSpace`,
`lemma-affine-space-etale-localization--1`), so the two right adjoints agree. In particular the
isomorphism holds for every `K`, constructible or not. -/
theorem nonempty_iso_rightDerivedUpperShriek_affineLine [HasTateTwist.IsNormalized Λ]
    {k : Type u} [Field k]
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of k)) [IsSeparated aY] [LocallyOfFiniteType aY]
    [HasInvertibleExponent Λ Y]
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (_hK : DerivedCategory.boundedConstructibleFiniteTor Λ Y K) :
    Nonempty ((rightDerivedUpperShriek Λ
          (𝔸(ULift.{u} (Fin 1); Y) ↘ Y)).obj K ≅
      (twistShift Λ 𝔸(ULift.{u} (Fin 1); Y) 1).obj
        ((L(((𝔸(ULift.{u} (Fin 1); Y) ↘ Y))^*[ModuleCat.{u + 1} Λ])).obj K)) := by
  obtain ⟨adj⟩ := nonempty_rightDerivedLowerShriek_adjunction_affineSpace Λ 1 Y
  exact ⟨((rightDerivedUpperShriekAdjunction _ _).rightAdjointUniq adj).app K⟩

omit [HasTateTwist Λ] in
/-- Blueprint `proposition-purity-vector-bundles`, Step 6: the projection of `𝔸^{d+1}_Y` is that of
`𝔸¹_{Y'}` followed by that of `Y' = 𝔸^d_Y`, so by the composition law and `Re^! ≅ Le^*` for the
isomorphism `e : 𝔸^{d+1}_Y ≅ 𝔸¹_{Y'}`, `Rp_{d+1}^! K ≅ Le^* Rp'^! Rp_d^! K`. -/
theorem nonempty_iso_rightDerivedUpperShriek_affineSpace_succ (d : ℕ) (Y : Scheme.{u})
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty ((rightDerivedUpperShriek Λ
          (𝔸(ULift.{u} (Fin (d + 1)); Y) ↘ Y)).obj K ≅
      (L(((affineSpaceSuccIso d Y).hom)^*[ModuleCat.{u + 1} Λ])).obj
        ((rightDerivedUpperShriek Λ
          (𝔸(ULift.{u} (Fin 1); 𝔸(ULift.{u} (Fin d); Y)) ↘ 𝔸(ULift.{u} (Fin d); Y))).obj
          ((rightDerivedUpperShriek Λ
            (𝔸(ULift.{u} (Fin d); Y) ↘ Y)).obj K))) := by
  set φ := affineSpaceSuccIso d Y
  set q := 𝔸(ULift.{u} (Fin 1); 𝔸(ULift.{u} (Fin d); Y)) ↘ 𝔸(ULift.{u} (Fin d); Y)
  set p := 𝔸(ULift.{u} (Fin d); Y) ↘ Y
  have : HasCompactification (φ.hom ≫ q) := HasCompactification.comp_of_isOpenImmersion q φ.hom
  have h : 𝔸(ULift.{u} (Fin (d + 1)); Y) ↘ Y = (φ.hom ≫ q) ≫ p := by
    rw [Category.assoc]
    exact (affineSpaceSuccIso_hom_over_over d Y).symm
  have : HasCompactification ((φ.hom ≫ q) ≫ p) := .of_eq h
  obtain ⟨heq⟩ := nonempty_iso_rightDerivedUpperShriek_of_eq Λ h
  obtain ⟨comp₁⟩ := nonempty_iso_rightDerivedUpperShriek_comp Λ
    (φ.hom ≫ q) p
  obtain ⟨comp₂⟩ := nonempty_iso_rightDerivedUpperShriek_comp Λ φ.hom q
  exact ⟨heq.app K ≪≫ comp₁.app K ≪≫ comp₂.app _ ≪≫ (rightDerivedUpperShriekIsoOfIso _ φ).app _⟩

omit [Finite Λ] in
/-- Blueprint `proposition-purity-vector-bundles`, Step 6: the twists of the two steps add up,

`Le^* ((Lp'^* (Lp_d^* K (d)[2d]))(1)[2]) ≅ Lp_{d+1}^* K (d + 1)[2(d + 1)]`. -/
theorem nonempty_iso_leftDerivedUpperStar_affineSpaceSuccIso_twistShift (d : ℕ)
    (Y : Scheme.{u}) [HasInvertibleExponent Λ Y]
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty ((L(((affineSpaceSuccIso d Y).hom)^*[ModuleCat.{u + 1} Λ])).obj
        ((twistShift Λ 𝔸(ULift.{u} (Fin 1); 𝔸(ULift.{u} (Fin d); Y)) 1).obj
          ((L(((𝔸(ULift.{u} (Fin 1); 𝔸(ULift.{u} (Fin d); Y)) ↘
            𝔸(ULift.{u} (Fin d); Y)))^*[ModuleCat.{u + 1} Λ])).obj
            ((twistShift Λ 𝔸(ULift.{u} (Fin d); Y) d).obj
              ((L(((𝔸(ULift.{u} (Fin d); Y) ↘ Y))^*[ModuleCat.{u + 1} Λ])).obj K)))) ≅
      (twistShift Λ 𝔸(ULift.{u} (Fin (d + 1)); Y) (d + 1 : ℕ)).obj
        ((L(((𝔸(ULift.{u} (Fin (d + 1)); Y) ↘ Y))^*[ModuleCat.{u + 1} Λ])).obj K)) := by
  set φ := affineSpaceSuccIso d Y
  set q := 𝔸(ULift.{u} (Fin 1); 𝔸(ULift.{u} (Fin d); Y)) ↘ 𝔸(ULift.{u} (Fin d); Y)
  set p := 𝔸(ULift.{u} (Fin d); Y) ↘ Y
  have h : 𝔸(ULift.{u} (Fin (d + 1)); Y) ↘ Y = φ.hom ≫ q ≫ p :=
    (affineSpaceSuccIso_hom_over_over d Y).symm
  -- the pullbacks compose: `Le^* Lq^* Lp^* ≅ L(e ≫ q ≫ p)^*`
  let pb : (L((φ.hom)^*[ModuleCat.{u + 1} Λ])).obj ((L((q)^*[ModuleCat.{u + 1} Λ])).obj
        ((L((p)^*[ModuleCat.{u + 1} Λ])).obj K)) ≅
      (L(((𝔸(ULift.{u} (Fin (d + 1)); Y) ↘ Y))^*[ModuleCat.{u + 1} Λ])).obj K :=
    (L((φ.hom)^*[ModuleCat.{u + 1} Λ])).mapIso
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) q p).app K).symm ≪≫
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) φ.hom (q ≫ p)
        (𝔸(ULift.{u} (Fin (d + 1)); Y) ↘ Y) h).app K).symm
  exact ⟨leftDerivedUpperStarTwistShiftIso Λ φ.hom 1 _ ≪≫
    (twistShift Λ _ 1).mapIso ((L((φ.hom)^*[ModuleCat.{u + 1} Λ])).mapIso
      (leftDerivedUpperStarTwistShiftIso Λ q d _) ≪≫
        leftDerivedUpperStarTwistShiftIso Λ φ.hom d _) ≪≫
    twistShiftTwistShiftIso Λ _ d 1 _ ≪≫
    (twistShift Λ _ _).mapIso pb ≪≫
    eqToIso (by push_cast; rfl)⟩

/-- Blueprint `proposition-purity-vector-bundles--1`: affine-space purity

This is clause (ii) of blueprint `proposition-purity-vector-bundles`. For the projection
`p_d : 𝔸^d_Y → Y`, `d ≥ 0`, of relative affine space over a separated scheme of finite type over a
field, on which the exponent of `Λ` is invertible, and `K ∈ D^b_{ctf}(Y, Λ)`,

`Rp_d^! K ≅ Lp_d^* K (d)[2d]`;

in particular `ω_{p_d} = Rp_d^! Λ_Y ≅ Λ(d)[2d]`. In the blueprint the isomorphism is the
comparison `γ_{p_d,K}` (`proposition-purity-vector-bundles--1`), the ordered composite of the
affine-line comparisons; these are not constructed, so only the existence of the isomorphism
is recorded.

The proof is Step 6 of the blueprint: write `𝔸^{d+1}_Y = 𝔸¹_{Y'}` with `Y' = 𝔸^d_Y`, apply
affine-line purity (`lemma-affine-space-etale-localization--1`) over `Y'` to
`Rp_d^! K ≅ Lp_d^* K (d)[2d]`, which lies in `D^b_{ctf}`, and add up the twists. -/
theorem nonempty_iso_rightDerivedUpperShriek_affineSpace [HasTateTwist.IsNormalized Λ]
    {k : Type u} [Field k] (d : ℕ)
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of k)) [IsSeparated aY] [LocallyOfFiniteType aY]
    [HasInvertibleExponent Λ Y]
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ Y K) :
    Nonempty ((rightDerivedUpperShriek Λ
          (𝔸(ULift.{u} (Fin d); Y) ↘ Y)).obj K ≅
      (twistShift Λ 𝔸(ULift.{u} (Fin d); Y) d).obj
        ((L(((𝔸(ULift.{u} (Fin d); Y) ↘ Y))^*[ModuleCat.{u + 1} Λ])).obj K)) := by
  induction d with
  | zero =>
    let e := asIso (𝔸(ULift.{u} (Fin 0); Y) ↘ Y)
    exact ⟨(rightDerivedUpperShriekIsoOfIso _ e).app K ≪≫
      (twistShiftZeroIso Λ _ (by simp) _).symm⟩
  | succ d ih =>
    obtain ⟨ih⟩ := ih
    obtain ⟨t⟩ := nonempty_iso_rightDerivedUpperShriek_affineSpace_succ Λ d Y K
    obtain ⟨l⟩ := nonempty_iso_rightDerivedUpperShriek_affineLine Λ 𝔸(ULift.{u} (Fin d); Y)
      (𝔸(ULift.{u} (Fin d); Y) ↘ Y ≫ aY) _
      (boundedConstructibleFiniteTor_twistShift_leftDerivedUpperStar Λ _ d hK)
    obtain ⟨s⟩ := nonempty_iso_leftDerivedUpperStar_affineSpaceSuccIso_twistShift Λ d Y K
    exact ⟨t ≪≫ (L(((affineSpaceSuccIso d Y).hom)^*[ModuleCat.{u + 1} Λ])).mapIso
      ((rightDerivedUpperShriek Λ (𝔸(ULift.{u} (Fin 1);
        𝔸(ULift.{u} (Fin d); Y)) ↘ 𝔸(ULift.{u} (Fin d); Y))).mapIso ih ≪≫ l) ≪≫ s⟩

/-- Blueprint `proposition-purity-vector-bundles--1`: affine-space purity

*The dualizing complex.* For the projection `p_d : 𝔸^d_Y → Y` of relative affine space over
a separated scheme of finite type over a field, on which the exponent of `Λ` is invertible,

`ω_{p_d} = Rp_d^! Λ_Y ≅ Λ_{𝔸^d_Y}(d)[2d]`.

This is the case `K = Λ_Y` of
`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_affineSpace`, with
`Lp_d^* Λ_Y ≅ Λ_{𝔸^d_Y}`; `Λ_Y` lies in `D^b_{ctf}` as the twisting object `Λ_Y(0)`. -/
theorem nonempty_iso_dualizingComplex_affineSpace [HasTateTwist.IsNormalized Λ]
    {k : Type u} [Field k] (d : ℕ)
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of k)) [IsSeparated aY] [LocallyOfFiniteType aY]
    [HasInvertibleExponent Λ Y] :
    Nonempty (dualizingComplex Λ (𝔸(ULift.{u} (Fin d); Y) ↘ Y) ≅
      (twistShift Λ 𝔸(ULift.{u} (Fin d); Y) d).obj
        (constantComplex Λ 𝔸(ULift.{u} (Fin d); Y))) := by
  obtain ⟨e⟩ := nonempty_iso_rightDerivedUpperShriek_affineSpace Λ d Y aY (tateObject Λ Y 0)
    (boundedConstructibleFiniteTor_tateObject Λ Y 0)
  exact ⟨(rightDerivedUpperShriek _ _).mapIso (HasTateTwist.twistObjectZeroIso Y).symm ≪≫ e ≪≫
    (twistShift Λ _ d).mapIso ((L(((𝔸(ULift.{u} (Fin d); Y) ↘ Y))^*[ModuleCat.{u + 1} Λ])).mapIso
      (HasTateTwist.twistObjectZeroIso Y) ≪≫ leftDerivedUpperStarUnitIso _ _)⟩

/-- Blueprint `proposition-smooth-purity-finite-coefficients`: Finite-coefficient smooth purity

*Step 3, the standard pair.* For the projection `π : 𝔸^c_B ⟶ B` of a trivial vector bundle of
rank `c` with zero section `0`, over a separated scheme of finite type over a field, the
section invariant is the Tate twist:

`𝒞(π, 0) = L0^* ω_π ≅ L0^* Λ(c)[2c] ≅ Λ_B(c)[2c]`,

by affine-space purity (`AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_affineSpace`)
and the compatibility of the twist with pullback. -/
theorem nonempty_iso_sectionInvariant_affineSpace [HasTateTwist.IsNormalized Λ]
    {k : Type u} [Field k] (c : ℕ)
    (B : Scheme.{u}) (aB : B ⟶ Spec (.of k)) [IsSeparated aB] [LocallyOfFiniteType aB]
    [HasInvertibleExponent Λ B] :
    Nonempty (sectionInvariant Λ (𝔸(ULift.{u} (Fin c); B) ↘ B)
        (AffineSpace.zeroSection (ULift.{u} (Fin c)) B) ≅
      (twistShift Λ B c).obj (constantComplex Λ B)) := by
  obtain ⟨e⟩ := nonempty_iso_dualizingComplex_affineSpace Λ c B aB
  exact ⟨(L((AffineSpace.zeroSection (ULift.{u} (Fin c)) B)^*[ModuleCat.{u + 1} Λ])).mapIso
      (e ≪≫ twistShiftConstantComplexIso Λ _ _) ≪≫
    leftDerivedUpperStarTateShiftIso Λ _ _ ≪≫ (twistShiftConstantComplexIso Λ B _).symm⟩

end Etale

end AlgebraicGeometry

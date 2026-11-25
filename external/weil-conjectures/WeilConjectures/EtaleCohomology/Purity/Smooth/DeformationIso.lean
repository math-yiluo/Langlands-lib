/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.Deformation
public import WeilConjectures.EtaleCohomology.Purity.Smooth.SectionInvariantBaseChange

/-!
# The DNC isomorphism as data

`WeilConjectures.EtaleCohomology.Purity.Smooth.Deformation` proves that the section invariant
`𝒞(g, s) = Ls^* ω_g` of a smooth morphism with a closed section is isomorphic to the section
invariant `𝒞(π_N, 0_N)` of its normal cone, by an isomorphism which is unique once normalized in
coordinates. This file makes the isomorphism and its ingredients into definitions.

* The fibre identifications of the family object `F = Ls̃^* ω_{g̃}` at `t = 1` and `t = 0` are
  the canonical base change isomorphisms of section invariants
  (`AlgebraicGeometry.Etale.sectionInvariantBaseChangeIso`), built from the base change map of
  `Rf^!` (`AlgebraicGeometry.Etale.dualizingComplexBaseChangeMap`), which is invertible for smooth
  `f` (`proposition-exceptional-inverse-image-smooth-morphism` (c)).
* The constancy comparison `κ : F ≅ La^* 𝒞(g, s)` is the unique one normalized at `t = 1`
  (`lemma-section-normal-bundle--1` (2), (3)).
* The DNC isomorphism is `(i₀^* κ)⁻¹` read through the fibre identification at `t = 0`
  (blueprint `lemma-section-normal-bundle--1`), and it is the identity of the standard object in
  every system of coordinates (`lemma-section-normal-bundle--1`).

## Main definitions

In the list below, `DeformationToNormalConeData` abbreviates
`AlgebraicGeometry.Scheme.Hom.DeformationToNormalConeData`.

- `DeformationToNormalConeData.oneFibreIso`, `DeformationToNormalConeData.zeroFibreIso`: the
  fibres of the family object at `t = 1` and `t = 0`.
- `DeformationToNormalConeData.familyObjectIso`: the normalized constancy comparison `κ`.
- `DeformationToNormalConeData.sectionInvariantIsoOfFibreIso`,
  `DeformationToNormalConeData.sectionInvariantIso`: the DNC isomorphism
  `𝒞(g, s) ≅ 𝒞(π_N, 0_N)`.

## Main statements

- `DeformationToNormalConeData.leftDerivedUpperStar_mapIso_sectionInvariantIsoOfFibreIso`: the
  DNC isomorphism is the identity of the standard object in coordinates, over every base change.
- `DeformationToNormalConeData.eq_sectionInvariantIsoOfFibreIso`: it is the only such
  isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Scheme.Hom.DeformationToNormalConeData

open _root_.AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {V B : Scheme.{u}} {d : ℕ}
  {g : V ⟶ B} {s : B ⟶ V} {N : NormalConeData d s} (D : DeformationToNormalConeData d g s N)
  [HasInvertibleExponent Λ B]

section Fibres

variable [QuasiSeparatedSpace B]

/-- The base change map of `ω_{g̃}` along a cartesian square over `𝔸¹_B` is invertible, `g̃`
being smooth. -/
theorem isIso_dualizingComplexBaseChangeMap {X' Y' : Scheme.{u}} {v : Y' ⟶ 𝔸(ULift.{u} (Fin 1); B)}
    {f' : X' ⟶ Y'} {v' : X' ⟶ D.scheme} [HasCompactification f'] [QuasiCompact f']
    (sq : IsPullback v' f' D.proj v) : IsIso (dualizingComplexBaseChangeMap Λ sq) :=
  have := D.hasInvertibleExponent_scheme Λ
  have : QuasiSeparatedSpace 𝔸(ULift.{u} (Fin 1); B) :=
    quasiSeparatedSpace_of_quasiSeparated (𝔸(ULift.{u} (Fin 1); B) ↘ B)
  isIso_dualizingComplexBaseChangeMap_of_smoothOfRelativeDimension Λ d sq

/-- Blueprint `prose-09-12` (1): the fibre of the family object at `t = 1` is
the section invariant of `(g, s)`, `θ₁ : Li₁^* F ≅ 𝒞(g, s)`, by base change for the smooth `g̃`
along the unit section. -/
noncomputable def oneFibreIso [HasCompactification g] [QuasiCompact g] :
    (L((AffineSpace.oneSection (ULift.{u} (Fin 1)) B)^*[ModuleCat.{u + 1} Λ])).obj
      (D.familyObject Λ) ≅ sectionInvariant Λ g s :=
  have := D.isIso_dualizingComplexBaseChangeMap Λ D.isPullback_oneFibre
  sectionInvariantBaseChangeIso Λ D.isPullback_oneFibre D.sect s D.comp_oneFibre

/-- Blueprint `prose-09-12` (1): the fibre of the family object at `t = 0` is
the section invariant of the normal cone, `θ₀ : Li₀^* F ≅ 𝒞(π_N, 0_N)`, by base change for the
smooth `g̃` along the zero section. -/
noncomputable def zeroFibreIso [HasCompactification N.proj] [QuasiCompact N.proj] :
    (L((AffineSpace.zeroSection (ULift.{u} (Fin 1)) B)^*[ModuleCat.{u + 1} Λ])).obj
      (D.familyObject Λ) ≅ sectionInvariant Λ N.proj N.zeroSection :=
  have := D.isIso_dualizingComplexBaseChangeMap Λ D.isPullback_zeroFibre
  sectionInvariantBaseChangeIso Λ D.isPullback_zeroFibre D.sect N.zeroSection D.comp_zeroFibre

end Fibres

variable [HasTateTwist Λ] [HasTateTwist.IsNormalized Λ] [HasCompactification g]
  {k : Type u} [Field k] (aB : B ⟶ Spec (.of k)) [IsSeparated aB] [LocallyOfFiniteType aB]
  [QuasiCompact D.proj]

/-- Blueprint `lemma-section-normal-bundle--1` (2), (3): the constancy comparison
`κ : F ≅ La^* 𝒞(g, s)` of the family object, the unique one restricting at `t = 1` to a given
identification `θ : Li₁^* F ≅ 𝒞(g, s)` (`existsUnique_familyObject_iso`). -/
noncomputable def familyObjectIso
    (θ : (L((AffineSpace.oneSection (ULift.{u} (Fin 1)) B)^*[ModuleCat.{u + 1} Λ])).obj
      (D.familyObject Λ) ≅ sectionInvariant Λ g s) :
    D.familyObject Λ ≅
      (L((𝔸(ULift.{u} (Fin 1); B) ↘ B)^*[ModuleCat.{u + 1} Λ])).obj (sectionInvariant Λ g s) :=
  (D.existsUnique_familyObject_iso Λ aB θ).exists.choose

/-- The constancy comparison restricts to `θ` at `t = 1`. -/
theorem leftDerivedUpperStar_map_familyObjectIso_hom_comp
    (θ : (L((AffineSpace.oneSection (ULift.{u} (Fin 1)) B)^*[ModuleCat.{u + 1} Λ])).obj
      (D.familyObject Λ) ≅ sectionInvariant Λ g s) :
    (L((AffineSpace.oneSection (ULift.{u} (Fin 1)) B)^*[ModuleCat.{u + 1} Λ])).map
        (D.familyObjectIso Λ aB θ).hom ≫
      (leftDerivedUpperStarCompSectionIso _ _ _
        (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) B)).hom.app _ = θ.hom :=
  (D.existsUnique_familyObject_iso Λ aB θ).exists.choose_spec

/-- The constancy comparison is the only comparison restricting to `θ` at `t = 1`. -/
theorem eq_familyObjectIso
    (θ : (L((AffineSpace.oneSection (ULift.{u} (Fin 1)) B)^*[ModuleCat.{u + 1} Λ])).obj
      (D.familyObject Λ) ≅ sectionInvariant Λ g s)
    (κ : D.familyObject Λ ≅
      (L((𝔸(ULift.{u} (Fin 1); B) ↘ B)^*[ModuleCat.{u + 1} Λ])).obj (sectionInvariant Λ g s))
    (hκ : (L((AffineSpace.oneSection (ULift.{u} (Fin 1)) B)^*[ModuleCat.{u + 1} Λ])).map κ.hom ≫
      (leftDerivedUpperStarCompSectionIso _ _ _
        (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) B)).hom.app _ = θ.hom) :
    κ = D.familyObjectIso Λ aB θ :=
  (D.existsUnique_familyObject_iso Λ aB θ).unique hκ
    (D.leftDerivedUpperStar_map_familyObjectIso_hom_comp Λ aB θ)

variable [HasCompactification N.proj]

/-- Blueprint `lemma-section-normal-bundle--1`: the DNC isomorphism `𝒞(g, s) ≅ 𝒞(π_N, 0_N)` attached
to identifications `θ₁ : Li₁^* F ≅ 𝒞(g, s)` and `θ₀ : Li₀^* F ≅ 𝒞(π_N, 0_N)` of the two fibres of
the family object: the inverse of the restriction `Li₀^* κ` of the constancy comparison
normalized against `θ₁`, read through `θ₀`,

`𝒞(g, s) ≅ Li₀^* La^* 𝒞(g, s) ≅ Li₀^* F ≅ 𝒞(π_N, 0_N)`. -/
noncomputable def sectionInvariantIsoOfFibreIso
    (θ₁ : (L((AffineSpace.oneSection (ULift.{u} (Fin 1)) B)^*[ModuleCat.{u + 1} Λ])).obj
      (D.familyObject Λ) ≅ sectionInvariant Λ g s)
    (θ₀ : (L((AffineSpace.zeroSection (ULift.{u} (Fin 1)) B)^*[ModuleCat.{u + 1} Λ])).obj
      (D.familyObject Λ) ≅ sectionInvariant Λ N.proj N.zeroSection) :
    sectionInvariant Λ g s ≅ sectionInvariant Λ N.proj N.zeroSection :=
  ((L((AffineSpace.zeroSection (ULift.{u} (Fin 1)) B)^*[ModuleCat.{u + 1} Λ])).mapIso
      (D.familyObjectIso Λ aB θ₁) ≪≫ (leftDerivedUpperStarCompSectionIso _ _ _
        (AffineSpace.zeroSection_comp_over (ULift.{u} (Fin 1)) B)).app
          (sectionInvariant Λ g s)).symm ≪≫ θ₀

/-- Blueprint `lemma-section-normal-bundle--1`: *normalization in coordinates and base change.* For
every base change `u : B' ⟶ B` and every `e : Lv₁^* F ≅ La'^* C₀` carrying the restricted
family to one pulled back from `C₀` on `B'`, reading `e` at `t = 1` and at `t = 0` as
`φ₁ : Lu^* 𝒞(g, s) ≅ C₀` and `φ₀ : Lu^* 𝒞(π_N, 0_N) ≅ C₀`, the DNC isomorphism restricts to
`Lu^* Ψ = φ₁ ≫ φ₀⁻¹`: in coordinates it is the identity of the standard object. -/
theorem leftDerivedUpperStar_mapIso_sectionInvariantIsoOfFibreIso
    (θ₁ : (L((AffineSpace.oneSection (ULift.{u} (Fin 1)) B)^*[ModuleCat.{u + 1} Λ])).obj
      (D.familyObject Λ) ≅ sectionInvariant Λ g s)
    (θ₀ : (L((AffineSpace.zeroSection (ULift.{u} (Fin 1)) B)^*[ModuleCat.{u + 1} Λ])).obj
      (D.familyObject Λ) ≅ sectionInvariant Λ N.proj N.zeroSection)
    {B' : Scheme.{u}} (u : B' ⟶ B)
    {C₀ : _root_.DerivedCategory (Sheaf B'.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (e : (L((AffineSpace.map (ULift.{u} (Fin 1)) u)^*[ModuleCat.{u + 1} Λ])).obj
      (D.familyObject Λ) ≅
        (L((𝔸(ULift.{u} (Fin 1); B') ↘ B')^*[ModuleCat.{u + 1} Λ])).obj C₀) :
    (L((u)^*[ModuleCat.{u + 1} Λ])).mapIso (D.sectionInvariantIsoOfFibreIso Λ aB θ₁ θ₀) =
      sectionRestrictionIso _ u _ (AffineSpace.oneSection_comp_map u)
          (AffineSpace.oneSection_comp_over _ B') θ₁ e ≪≫
        (sectionRestrictionIso _ u _ (AffineSpace.zeroSection_comp_map u)
          (AffineSpace.zeroSection_comp_over _ B') θ₀ e).symm := by
  have := D.hasInvertibleExponent_scheme Λ
  let κ := D.familyObjectIso Λ aB θ₁
  have hθ₁ : θ₁ = (L((AffineSpace.oneSection (ULift.{u} (Fin 1)) B)^*[ModuleCat.{u + 1} Λ])).mapIso
      κ ≪≫ (leftDerivedUpperStarCompSectionIso _ _ _
        (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) B)).app _ :=
    Iso.ext (D.leftDerivedUpperStar_map_familyObjectIso_hom_comp Λ aB θ₁).symm
  let θ₀' := (L((AffineSpace.zeroSection (ULift.{u} (Fin 1)) B)^*[ModuleCat.{u + 1} Λ])).mapIso
      κ ≪≫ (leftDerivedUpperStarCompSectionIso _ _ _
        (AffineSpace.zeroSection_comp_over (ULift.{u} (Fin 1)) B)).app (sectionInvariant Λ g s)
  change (L((u)^*[ModuleCat.{u + 1} Λ])).mapIso (θ₀'.symm ≪≫ θ₀) = _
  have : HasInvertibleExponent Λ B' := .of_hom u
  have hv : AffineSpace.map (ULift.{u} (Fin 1)) u ≫ 𝔸(ULift.{u} (Fin 1); B) ↘ B =
      𝔸(ULift.{u} (Fin 1); B') ↘ B' ≫ u := AffineSpace.map_over u
  let κr := (L((AffineSpace.map (ULift.{u} (Fin 1)) u)^*[ModuleCat.{u + 1} Λ])).mapIso κ ≪≫
    ((leftDerivedUpperStarComp _ (AffineSpace.map (ULift.{u} (Fin 1)) u)
      (𝔸(ULift.{u} (Fin 1); B) ↘ B)).app _).symm ≪≫
    (leftDerivedUpperStarComp _ (𝔸(ULift.{u} (Fin 1); B') ↘ B') u _ hv).app _
  let φ₁ := sectionRestrictionIso _ u _ (AffineSpace.oneSection_comp_map u)
    (AffineSpace.oneSection_comp_over _ B') θ₁ e
  -- the restriction of `κ` is `e` read in the coordinates `φ₁`
  have hκr : κr = e ≪≫
      (L((𝔸(ULift.{u} (Fin 1); B') ↘ B')^*[ModuleCat.{u + 1} Λ])).mapIso φ₁.symm := by
    refine eq_of_leftDerivedUpperStar_oneSection_eq Λ _ _
      (DerivedCategory.isInvertible.leftDerivedUpperStar _ (D.isInvertible_familyObject Λ))
      _ _ (leftDerivedUpperStar_map_eq_of_sectionRestrictionIso_eq _ u _
        (AffineSpace.oneSection_comp_map u) (AffineSpace.oneSection_comp_over _ B') θ₁ _ _ ?_)
    rw [sectionRestrictionIso_trans_right, hθ₁, sectionRestrictionIso_restrict _ u _ _ _ hv
      (AffineSpace.oneSection_comp_over _ B), ← hθ₁]
    exact (Iso.self_symm_id φ₁).symm
  have he : e = κr ≪≫
      (L((𝔸(ULift.{u} (Fin 1); B') ↘ B')^*[ModuleCat.{u + 1} Λ])).mapIso φ₁ := by
    rw [hκr]
    ext
    simp
  have key : sectionRestrictionIso _ u _ (AffineSpace.zeroSection_comp_map u)
        (AffineSpace.zeroSection_comp_over _ B') θ₀ e =
      (L((u)^*[ModuleCat.{u + 1} Λ])).mapIso (θ₀'.symm ≪≫ θ₀).symm ≪≫ φ₁ := by
    have h₀ : θ₀ = θ₀' ≪≫ (θ₀'.symm ≪≫ θ₀) := by simp
    calc _ = sectionRestrictionIso _ u _ (AffineSpace.zeroSection_comp_map u)
          (AffineSpace.zeroSection_comp_over _ B') (θ₀' ≪≫ (θ₀'.symm ≪≫ θ₀))
            (κr ≪≫ (L((𝔸(ULift.{u} (Fin 1); B') ↘ B')^*[ModuleCat.{u + 1} Λ])).mapIso φ₁) := by
          rw [← he, ← h₀]
      _ = _ := by
        rw [sectionRestrictionIso_trans_left, sectionRestrictionIso_trans_right,
          sectionRestrictionIso_restrict _ u _ _ _ hv (AffineSpace.zeroSection_comp_over _ B)]
        simp
  rw [key]
  ext
  simp

/-- Blueprint `lemma-section-normal-bundle--1`: *uniqueness.* For coordinates `e` over a surjective
`u : B' ⟶ B`, the DNC isomorphism is the only isomorphism `𝒞(g, s) ≅ 𝒞(π_N, 0_N)` which is the
identity of the standard object in these coordinates. -/
theorem eq_sectionInvariantIsoOfFibreIso [SmoothOfRelativeDimension d g]
    (θ₁ : (L((AffineSpace.oneSection (ULift.{u} (Fin 1)) B)^*[ModuleCat.{u + 1} Λ])).obj
      (D.familyObject Λ) ≅ sectionInvariant Λ g s)
    (θ₀ : (L((AffineSpace.zeroSection (ULift.{u} (Fin 1)) B)^*[ModuleCat.{u + 1} Λ])).obj
      (D.familyObject Λ) ≅ sectionInvariant Λ N.proj N.zeroSection)
    {B' : Scheme.{u}} (u : B' ⟶ B) [Surjective u]
    {C₀ : _root_.DerivedCategory (Sheaf B'.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (e : (L((AffineSpace.map (ULift.{u} (Fin 1)) u)^*[ModuleCat.{u + 1} Λ])).obj
      (D.familyObject Λ) ≅
        (L((𝔸(ULift.{u} (Fin 1); B') ↘ B')^*[ModuleCat.{u + 1} Λ])).obj C₀)
    (Ψ : sectionInvariant Λ g s ≅ sectionInvariant Λ N.proj N.zeroSection)
    (hΨ : (L((u)^*[ModuleCat.{u + 1} Λ])).mapIso Ψ =
      sectionRestrictionIso _ u _ (AffineSpace.oneSection_comp_map u)
          (AffineSpace.oneSection_comp_over _ B') θ₁ e ≪≫
        (sectionRestrictionIso _ u _ (AffineSpace.zeroSection_comp_map u)
          (AffineSpace.zeroSection_comp_over _ B') θ₀ e).symm) :
    Ψ = D.sectionInvariantIsoOfFibreIso Λ aB θ₁ θ₀ :=
  (existsUnique_iso_sectionInvariant_normalCone Λ d g s N D aB θ₁ θ₀ u e).unique hΨ
    (D.leftDerivedUpperStar_mapIso_sectionInvariantIsoOfFibreIso Λ aB θ₁ θ₀ u e)

/-- Blueprint `lemma-section-normal-bundle`, `lemma-section-normal-bundle--1`: the DNC isomorphism
`δ_{g,s} : 𝒞(g, s) ≅ 𝒞(π_N, 0_N)` for the canonical fibre identifications `oneFibreIso` and
`zeroFibreIso` of the family object. -/
noncomputable def sectionInvariantIso :
    sectionInvariant Λ g s ≅ sectionInvariant Λ N.proj N.zeroSection :=
  have := quasiSeparatedSpace_of_quasiSeparated aB
  have : QuasiCompact g := MorphismProperty.of_isPullback D.isPullback_oneFibre inferInstance
  have : QuasiCompact N.proj :=
    MorphismProperty.of_isPullback D.isPullback_zeroFibre inferInstance
  D.sectionInvariantIsoOfFibreIso Λ aB (D.oneFibreIso Λ) (D.zeroFibreIso Λ)

end Scheme.Hom.DeformationToNormalConeData

end AlgebraicGeometry

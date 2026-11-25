/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.RegularImmersion
public import WeilConjectures.Compactification.Affine
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.AlgebraicGeometry.DeformationSpace
public import WeilConjectures.AlgebraicGeometry.DeformationSpace.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.Compactification.NagataCompactification

/-!
# Deformation to the normal cone of a section

For a smooth morphism `g : V ⟶ B` with a closed section `s : B ⟶ V`, the *deformation to the
normal cone of the section* is

`𝒟_s V = Bl_{s(B) × {0}} (V ×_B 𝔸¹_B) ∖ (strict transform of the closed fibre)`,

the blow-up of `V ×_B 𝔸¹_B` along `s(B) × {0}` with the strict transform of the fibre over
`t = 0` removed. It carries a morphism `g̃ : 𝒟_s V ⟶ 𝔸¹_B` with a section
`s̃ : 𝔸¹_B ⟶ 𝒟_s V`; the fibre of `(g̃, s̃)` over `t = 1` is `(g, s)` and the fibre over
`t = 0` is `(π_N, 0_N)`, so the deformation interpolates between a smooth morphism with a
section and a vector bundle with its zero section.

Equivalently `𝒟_s V = Spec_V (⨁_{r ∈ ℤ} I_s^r t^{-r})` is the extended Rees construction,
with `I_s^r = 𝒪_V` for `r ≤ 0`; inverting `t` gives `V × 𝔾_m` and setting `t = 0` gives the
normal cone.

## Implementation notes

The deformation space is constructed as the relative spectrum `D_s V = Spec_V 𝒪_V[t, I t⁻¹]`
of the extended Rees algebra of the ideal `I` of `s(B)`
(`AlgebraicGeometry.Scheme.IdealSheafData.deformationSpace`), and the normal cone `N_s` as the
relative spectrum of `𝒪_V[t, I t⁻¹] / t = ⨁_{r ≥ 0} I^r / I^{r+1}`, which lies over `s(B) ≅ B`
(`AlgebraicGeometry.Scheme.Hom.normalConeData`). The fibre squares come from pushout squares of
quasi-coherent algebras. Smoothness of `g̃` is proved on charts: near `s(B)` there are étale
coordinates in which `s` is the origin, and there the deformation space is étale over
`𝔸^d × 𝔸¹` (`AlgebraicGeometry.exists_smoothOfRelativeDimension_extendedReesAlgebra_of_section`).

The structure `AlgebraicGeometry.Scheme.Hom.DeformationToNormalConeData` records the clauses of
`prose-09-12` about the deformation; the blueprint lemma is the statement that such a datum
exists with the normal cone of `s` as fibre over `t = 0`. The punctured trivialisation `κ°` of
`prose-09-12` (3) — the identification of the deformation over `𝔾_{m,B}` with
`V ×_B 𝔾_{m,B}` — is a field. `𝔾_m` is not a Mathlib scheme, so `𝔾_{m,B}` is carried as an open
subscheme of `𝔸¹_B` whose underlying set is the complement of the zero section, as in
`WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine`.

## Main definitions

- `AlgebraicGeometry.Scheme.Hom.normalConeData`: the normal cone of a closed section.
- `AlgebraicGeometry.Scheme.Hom.DeformationToNormalConeData`: the deformation space `𝒟_s V`
  together with `g̃`, `s̃` and the properties characterising them.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.smoothOfRelativeDimension_deformationSpaceProj`
- `AlgebraicGeometry.Scheme.Hom.normalConeData`
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {V B : Scheme.{u}}

namespace Scheme.Hom

/-! ### The construction -/

section Construction

open AffineZariskiSite

variable (g : V ⟶ B) (s : B ⟶ V)

/-- The projection `g̃ : D_s V ⟶ 𝔸¹_B` of the deformation space of the section `s`, given by the
coordinate `t` and `D_s V ⟶ V ⟶ B`. -/
noncomputable def deformationSpaceProj : s.ker.deformationSpace ⟶ 𝔸(ULift.{u} (Fin 1); B) :=
  s.ker.deformationSpaceToPolynomialSpec ≫ V.polynomialSpecToAffineSpace ≫
    AffineSpace.map (ULift.{u} (Fin 1)) g

/-- `B` is the closed subscheme `V(I_s) = Spec_V (𝒪_V / I_s)`. -/
noncomputable def toQuotientSpec : B ⟶ s.ker.quotientSpec :=
  IsClosedImmersion.lift (relativeGluingData s.ker.coequifibered_toQuotientAlgebra).toBase s
    (s.ker.ker_quotientSpec_toBase).le

@[reassoc (attr := simp)]
lemma toQuotientSpec_toBase :
    s.toQuotientSpec ≫ (relativeGluingData s.ker.coequifibered_toQuotientAlgebra).toBase = s :=
  IsClosedImmersion.lift_fac _ _ _

instance [IsClosedImmersion s] : IsIso s.toQuotientSpec :=
  IsClosedImmersion.isIso_of_ker_eq _ _ _ (s.toQuotientSpec_toBase)
    (s.ker.ker_quotientSpec_toBase).symm

/-- The projection `N_s ⟶ B` of the normal cone of the section. -/
noncomputable def normalConeProj : s.ker.normalCone ⟶ B :=
  (relativeGluingData s.ker.coequifibered_toNormalConePresheaf).toBase ≫ g

/-- The zero section `B ⟶ N_s` of the normal cone, given by the degree-zero part
`⨁_{r ≥ 0} I^r / I^{r+1} ⟶ 𝒪_V / I`. -/
noncomputable def normalConeZeroSection : B ⟶ s.ker.normalCone :=
  s.toQuotientSpec ≫ relativeGluingMap s.ker.coequifibered_toNormalConePresheaf
    s.ker.coequifibered_toQuotientAlgebra s.ker.normalConeToQuotient


@[reassoc (attr := simp)]
lemma normalConeZeroSection_toBase :
    s.normalConeZeroSection ≫ (relativeGluingData s.ker.coequifibered_toNormalConePresheaf).toBase =
      s := by
  rw [normalConeZeroSection, Category.assoc,
    relativeGluingMap_toBase _ _ _ s.ker.toNormalConePresheaf_comp_normalConeToQuotient,
    toQuotientSpec_toBase]

variable {g s} in
lemma normalConeZeroSection_normalConeProj (hs : s ≫ g = 𝟙 B) :
    s.normalConeZeroSection ≫ normalConeProj g s = 𝟙 B := by
  rw [normalConeProj, normalConeZeroSection_toBase_assoc, hs]

instance [IsClosedImmersion s] : IsClosedImmersion s.normalConeZeroSection := by
  have : IsClosedImmersion (s.normalConeZeroSection ≫
      (relativeGluingData s.ker.coequifibered_toNormalConePresheaf).toBase) := by
    rw [normalConeZeroSection_toBase]; infer_instance
  exact IsClosedImmersion.of_comp _
    (relativeGluingData s.ker.coequifibered_toNormalConePresheaf).toBase

/-- `𝔸¹_B ⟶ 𝔸¹_{V(I_s)} = Spec_V (𝒪_V / I_s)[t]`, the affine line over `B ≅ V(I_s)`. -/
noncomputable def affineSpaceToQuotientPolynomialSpec :
    𝔸(ULift.{u} (Fin 1); B) ⟶ s.ker.quotientPolynomialSpec :=
  s.ker.isPullback_quotientPolynomialSpec.lift
    ((𝔸(ULift.{u} (Fin 1); B) ↘ B) ≫ s.toQuotientSpec)
    (AffineSpace.map (ULift.{u} (Fin 1)) s ≫ inv V.polynomialSpecToAffineSpace) (by
      rw [Category.assoc, toQuotientSpec_toBase, Category.assoc,
        ← polynomialSpecToAffineSpace_over, IsIso.inv_hom_id_assoc, AffineSpace.map_over])

@[reassoc (attr := simp)]
lemma affineSpaceToQuotientPolynomialSpec_toQuotientSpec :
    s.affineSpaceToQuotientPolynomialSpec ≫ relativeGluingMap
      s.ker.coequifibered_toQuotientAlgebra s.ker.coequifibered_toQuotientPolynomialAlgebra
      (s.ker.quotientAlgebra.whiskerLeft CommRingCat.polynomialC) =
      (𝔸(ULift.{u} (Fin 1); B) ↘ B) ≫ s.toQuotientSpec :=
  IsPullback.lift_fst _ _ _ _

@[reassoc (attr := simp)]
lemma affineSpaceToQuotientPolynomialSpec_toPolynomialSpec :
    s.affineSpaceToQuotientPolynomialSpec ≫ relativeGluingMap
      V.coequifibered_toPolynomialPresheaf s.ker.coequifibered_toQuotientPolynomialAlgebra
      s.ker.polynomialToQuotientPolynomial =
      AffineSpace.map (ULift.{u} (Fin 1)) s ≫ inv V.polynomialSpecToAffineSpace :=
  IsPullback.lift_snd _ _ _ _

/-- The section `s̃ : 𝔸¹_B ⟶ D_s V` of `g̃`: on the extended Rees algebra it is
`𝒪_V[t, I t⁻¹] ⟶ (𝒪_V / I)[t]`, `t ↦ t`, `x t⁻¹ ↦ 0`. -/
noncomputable def deformationSpaceSection : 𝔸(ULift.{u} (Fin 1); B) ⟶ s.ker.deformationSpace :=
  s.affineSpaceToQuotientPolynomialSpec ≫ relativeGluingMap s.ker.coequifibered_toReesPresheaf
    s.ker.coequifibered_toQuotientPolynomialAlgebra s.ker.reesToQuotientPolynomial

lemma toReesPresheaf_comp_reesToQuotientPolynomial :
    s.ker.toReesPresheaf ≫ s.ker.reesToQuotientPolynomial = s.ker.toQuotientPolynomialAlgebra := by
  ext U x
  exact Ideal.extendedReesAlgebraToPolynomial_algebraMap (I := s.ker.siteIdeal U.unop) _
    Ideal.mk_ker.ge x

@[reassoc (attr := simp)]
lemma deformationSpaceSection_toPolynomialSpec :
    s.deformationSpaceSection ≫ s.ker.deformationSpaceToPolynomialSpec =
      AffineSpace.map (ULift.{u} (Fin 1)) s ≫ inv V.polynomialSpecToAffineSpace := by
  rw [deformationSpaceSection, IdealSheafData.deformationSpaceToPolynomialSpec, Category.assoc,
    ← relativeGluingMap_comp, s.ker.polynomialToRees_comp_reesToQuotientPolynomial,
    affineSpaceToQuotientPolynomialSpec_toPolynomialSpec]

@[reassoc (attr := simp)]
lemma deformationSpaceSection_toBase :
    s.deformationSpaceSection ≫ s.ker.deformationSpaceProj =
      (𝔸(ULift.{u} (Fin 1); B) ↘ B) ≫ s := by
  change _ ≫ (relativeGluingData s.ker.coequifibered_toReesPresheaf).toBase = _
  rw [← relativeGluingMap_toBase V.coequifibered_toPolynomialPresheaf
    s.ker.coequifibered_toReesPresheaf s.ker.polynomialToRees
    s.ker.toPolynomialPresheaf_comp_polynomialToRees,
    ← IdealSheafData.deformationSpaceToPolynomialSpec,
    deformationSpaceSection_toPolynomialSpec_assoc,
    show (relativeGluingData V.coequifibered_toPolynomialPresheaf).toBase =
      V.polynomialSpecToAffineSpace ≫ _ from V.polynomialSpecToAffineSpace_over.symm,
    IsIso.inv_hom_id_assoc, AffineSpace.map_over]

variable {g s} in
lemma deformationSpaceSection_deformationSpaceProj (hs : s ≫ g = 𝟙 B) :
    s.deformationSpaceSection ≫ deformationSpaceProj g s = 𝟙 _ := by
  rw [deformationSpaceProj, deformationSpaceSection_toPolynomialSpec_assoc,
    IsIso.inv_hom_id_assoc, ← AffineSpace.map_comp, hs, AffineSpace.map_id]

/-! #### The fibre over `t = 0` -/

/-- `Spec_V 𝒪_V[t] = V ×_B 𝔸¹_B`. -/
lemma isPullback_polynomialSpecProj :
    IsPullback V.polynomialSpecProj (V.polynomialSpecToAffineSpace ≫
      AffineSpace.map (ULift.{u} (Fin 1)) g) g (𝔸(ULift.{u} (Fin 1); B) ↘ B) := by
  refine (AffineSpace.isPullback_map (n := ULift.{u} (Fin 1)) g).flip.of_iso
    (asIso V.polynomialSpecToAffineSpace).symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
    (by simp) (by simp)
  · simp only [Iso.symm_hom, asIso_inv, Iso.refl_hom, Category.comp_id, IsIso.eq_inv_comp,
      polynomialSpecToAffineSpace_over]
  · simp

/-- The zero section of `Spec_V 𝒪_V[t]` is the base change of the zero section of `𝔸¹_B`. -/
lemma isPullback_polynomialSpecZeroSection :
    IsPullback V.polynomialSpecZeroSection g
      (V.polynomialSpecToAffineSpace ≫ AffineSpace.map (ULift.{u} (Fin 1)) g)
      (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B) := by
  refine IsPullback.of_right ?_ ?_ (isPullback_polynomialSpecProj g)
  · rw [polynomialSpecZeroSection, Category.assoc, ← polynomialSpecToAffineSpace_over,
      ← Category.assoc V.polynomialZeroSpecToPolynomialSpec,
      polynomialZeroSpecToPolynomialSpec_comp_polynomialSpecToAffineSpace, Category.assoc,
      AffineSpace.zeroSection_over, Category.comp_id, IsIso.inv_hom_id,
      AffineSpace.zeroSection_over]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  · rw [← Category.assoc, polynomialSpecZeroSection_comp_polynomialSpecToAffineSpace,
      AffineSpace.zeroSection_comp_map]

/-- **The fibre over `t = 0` is the normal cone.** -/
lemma isPullback_normalConeToDeformationSpace :
    IsPullback s.ker.normalConeToDeformationSpace (normalConeProj g s) (deformationSpaceProj g s)
      (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B) := by
  have h : IsPullback s.ker.normalConeToDeformationSpace
      (relativeGluingData s.ker.coequifibered_toNormalConePresheaf).toBase
      s.ker.deformationSpaceToPolynomialSpec V.polynomialSpecZeroSection :=
    s.ker.isPullback_normalConeToDeformationSpace.of_iso (Iso.refl _) (Iso.refl _)
      (asIso (relativeGluingData V.coequifibered_toPolynomialZeroPresheaf).toBase) (Iso.refl _)
      (by simp) (by
        simp only [asIso_hom, Iso.refl_hom, Category.id_comp,
          IdealSheafData.normalConeToPolynomialZeroSpec]
        exact relativeGluingMap_toBase _ _ _
          s.ker.toPolynomialZeroPresheaf_comp_polynomialZeroToNormalCone)
      (by simp) (by simp [polynomialSpecZeroSection])
  exact h.paste_vert (isPullback_polynomialSpecZeroSection g)

/-! #### The punctured trivialisation -/

/-- The punctured line `𝔾_{m,B} ⊆ 𝔸¹_B`, the locus where the coordinate is invertible. -/
noncomputable abbrev puncturedLine (B : Scheme.{u}) : (𝔸(ULift.{u} (Fin 1); B)).Opens :=
  (𝔸(ULift.{u} (Fin 1); B)).basicOpen (AffineSpace.coord B 0)

lemma coe_puncturedLine (B : Scheme.{u}) : (puncturedLine B : Set 𝔸(ULift.{u} (Fin 1); B)) =
    (Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B).base)ᶜ := by
  ext y
  have := congr(y ∈ $(AffineSpace.range_zeroSection (ULift.{u} (Fin 1)) B))
  simp only [Set.mem_ofPred_eq] at this
  rw [Set.mem_compl_iff, this]
  simp only [SetLike.mem_coe, not_forall, not_not]
  exact ⟨fun h ↦ ⟨0, h⟩, fun ⟨i, h⟩ ↦ by rwa [Subsingleton.elim i 0] at h⟩

lemma preimage_puncturedLine :
    (V.polynomialSpecToAffineSpace ≫ AffineSpace.map (ULift.{u} (Fin 1)) g) ⁻¹ᵁ puncturedLine B =
      V.laurentSpecToPolynomialSpec.opensRange := by
  rw [opensRange_laurentSpecToPolynomialSpec, Scheme.preimage_basicOpen_top,
    Scheme.Hom.comp_appTop, CommRingCat.comp_apply, AffineSpace.map_appTop_coord]
  rfl

/-- The punctured line of `Spec_V 𝒪_V[t]` maps to the one of `𝔸¹_B`. -/
noncomputable def laurentSpecToPuncturedLine : V.laurentSpec ⟶ puncturedLine B :=
  IsOpenImmersion.lift (puncturedLine B).ι (V.laurentSpecToPolynomialSpec ≫
    V.polynomialSpecToAffineSpace ≫ AffineSpace.map (ULift.{u} (Fin 1)) g) (by
      rw [Scheme.Opens.range_ι, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
        Set.image_subset_iff, ← Scheme.Hom.coe_opensRange, ← preimage_puncturedLine]
      rfl)

lemma isPullback_laurentSpecToPuncturedLine :
    IsPullback V.laurentSpecToPolynomialSpec (laurentSpecToPuncturedLine g)
      (V.polynomialSpecToAffineSpace ≫ AffineSpace.map (ULift.{u} (Fin 1)) g)
      (puncturedLine B).ι :=
  (IsOpenImmersion.isPullback _ _ _ _ (IsOpenImmersion.lift_fac _ _ _).symm
    (by rw [Scheme.Opens.opensRange_ι]; exact preimage_puncturedLine g)).flip

/-- The punctured line of `Spec_V 𝒪_V[t]` is `V ×_B 𝔾_{m,B}`. -/
lemma isPullback_laurentSpec :
    IsPullback (V.laurentSpecToPolynomialSpec ≫ V.polynomialSpecProj)
      (laurentSpecToPuncturedLine g) g ((puncturedLine B).ι ≫ 𝔸(ULift.{u} (Fin 1); B) ↘ B) :=
  (isPullback_laurentSpecToPuncturedLine g).paste_horiz (isPullback_polynomialSpecProj g)

/-- The punctured trivialisation `κ° : V ×_B 𝔾_{m,B} ⟶ D_s V`. -/
noncomputable def deformationSpaceGeneric :
    pullback g ((puncturedLine B).ι ≫ 𝔸(ULift.{u} (Fin 1); B) ↘ B) ⟶ s.ker.deformationSpace :=
  (isPullback_laurentSpec g).isoPullback.inv ≫ s.ker.laurentSpecToDeformationSpace

lemma isPullback_laurentSpecToDeformationSpace :
    IsPullback s.ker.laurentSpecToDeformationSpace (laurentSpecToPuncturedLine g)
      (deformationSpaceProj g s) (puncturedLine B).ι := by
  exact s.ker.isPullback_laurentSpecToDeformationSpace.paste_vert
    (isPullback_laurentSpecToPuncturedLine g)

/-- **The punctured trivialisation.** Over `𝔾_{m,B}` the deformation space is `V ×_B 𝔾_{m,B}`. -/
lemma isPullback_deformationSpaceGeneric :
    IsPullback (deformationSpaceGeneric g s) (pullback.snd _ _) (deformationSpaceProj g s)
      (puncturedLine B).ι :=
  (isPullback_laurentSpecToDeformationSpace g s).of_iso (isPullback_laurentSpec g).isoPullback
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp [deformationSpaceGeneric]) (by simp)
    (by simp) (by simp)

@[reassoc (attr := simp)]
lemma deformationSpaceGeneric_toBase :
    deformationSpaceGeneric g s ≫ s.ker.deformationSpaceProj = pullback.fst _ _ := by
  rw [deformationSpaceGeneric, Category.assoc, IdealSheafData.laurentSpecToDeformationSpace,
    relativeGluingMap_toBase _ _ _ s.ker.toReesPresheaf_comp_reesToLaurent,
    ← relativeGluingMap_toBase V.coequifibered_toPolynomialPresheaf _ _
      IdealSheafData.toPolynomialPresheaf_comp_polynomialToLaurent]
  exact (isPullback_laurentSpec g).isoPullback_inv_fst

/-! #### The fibre over `t = 1` -/

/-- The unit section `B ⟶ 𝔸¹_B` lands in the punctured line. -/
noncomputable def oneSectionToPuncturedLine (B : Scheme.{u}) : B ⟶ puncturedLine B :=
  IsOpenImmersion.lift (puncturedLine B).ι (AffineSpace.oneSection (ULift.{u} (Fin 1)) B) (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, rfl⟩
    change y ∈ AffineSpace.oneSection _ B ⁻¹ᵁ puncturedLine B
    rw [Scheme.preimage_basicOpen_top, AffineSpace.oneSection, AffineSpace.homOfVector_appTop_coord]
    simp)

@[reassoc (attr := simp)]
lemma oneSectionToPuncturedLine_ι (B : Scheme.{u}) :
    oneSectionToPuncturedLine B ≫ (puncturedLine B).ι = AffineSpace.oneSection _ B :=
  IsOpenImmersion.lift_fac _ _ _

@[reassoc (attr := simp)]
lemma oneSectionToPuncturedLine_ι_over (B : Scheme.{u}) :
    oneSectionToPuncturedLine B ≫ (puncturedLine B).ι ≫ 𝔸(ULift.{u} (Fin 1); B) ↘ B = 𝟙 B := by
  rw [oneSectionToPuncturedLine_ι_assoc, AffineSpace.oneSection_comp_over]

/-- The inclusion `ι₁ : V ⟶ D_s V` of the fibre over `t = 1`. -/
noncomputable def deformationSpaceOneFibre : V ⟶ s.ker.deformationSpace :=
  pullback.lift (𝟙 V) (g ≫ oneSectionToPuncturedLine B) (by
    rw [Category.assoc, oneSectionToPuncturedLine_ι_over, Category.id_comp,
      Category.comp_id]) ≫ deformationSpaceGeneric g s

/-- Pulling back a base change along a section gives back the source. -/
lemma isPullback_lift_of_section {X' Y' Z' : Scheme.{u}} (f : X' ⟶ Z') (h : Y' ⟶ Z')
    (σ : Z' ⟶ Y') (hσ : σ ≫ h = 𝟙 Z') :
    IsPullback (pullback.lift (𝟙 X') (f ≫ σ) (by simp [hσ])) f (pullback.snd f h) σ :=
  IsPullback.of_right (by simpa [hσ] using IsPullback.of_horiz_isIso (CommSq.mk (by simp)))
    (by simp) (IsPullback.of_hasPullback f h)

/-- **The fibre over `t = 1` is `(g, s)`.** -/
lemma isPullback_deformationSpaceOneFibre :
    IsPullback (deformationSpaceOneFibre g s) g (deformationSpaceProj g s)
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) B) := by
  have := (isPullback_lift_of_section g ((puncturedLine B).ι ≫ 𝔸(ULift.{u} (Fin 1); B) ↘ B)
    (oneSectionToPuncturedLine B) (oneSectionToPuncturedLine_ι_over B)).paste_horiz
      (isPullback_deformationSpaceGeneric g s)
  rwa [oneSectionToPuncturedLine_ι] at this

lemma laurentSpecToDeformationSpace_toBase :
    s.ker.laurentSpecToDeformationSpace ≫ s.ker.deformationSpaceProj =
      V.laurentSpecToPolynomialSpec ≫ V.polynomialSpecProj := by
  rw [IdealSheafData.laurentSpecToDeformationSpace,
    relativeGluingMap_toBase _ _ _ s.ker.toReesPresheaf_comp_reesToLaurent,
    laurentSpecToPolynomialSpec, relativeGluingMap_toBase _ _ _
      IdealSheafData.toPolynomialPresheaf_comp_polynomialToLaurent]

variable {g s} in
lemma comp_deformationSpaceOneFibre (hs : s ≫ g = 𝟙 B) :
    s ≫ deformationSpaceOneFibre g s =
      AffineSpace.oneSection (ULift.{u} (Fin 1)) B ≫ s.deformationSpaceSection := by
  have hP := isPullback_laurentSpecToDeformationSpace g s
  have hm : (AffineSpace.oneSection (ULift.{u} (Fin 1)) B ≫ s.deformationSpaceSection) ≫
      deformationSpaceProj g s = oneSectionToPuncturedLine B ≫ (puncturedLine B).ι := by
    rw [Category.assoc, deformationSpaceSection_deformationSpaceProj hs, Category.comp_id,
      oneSectionToPuncturedLine_ι]
  rw [← hP.lift_fst _ _ hm, deformationSpaceOneFibre, deformationSpaceGeneric]
  simp only [← Category.assoc]
  congr 1
  refine (isPullback_laurentSpec g).hom_ext ?_ ?_
  · rw [Category.assoc, IsPullback.isoPullback_inv_fst, ← laurentSpecToDeformationSpace_toBase,
      hP.lift_fst_assoc, Category.assoc, Category.assoc, deformationSpaceSection_toBase,
      ← Category.assoc (AffineSpace.oneSection _ B), AffineSpace.oneSection_comp_over,
      Category.id_comp]
    simp
  · rw [hP.lift_snd, Category.assoc, Category.assoc, IsPullback.isoPullback_inv_snd,
      pullback.lift_snd, reassoc_of% hs]

lemma zeroSection_comp_affineSpaceToQuotientPolynomialSpec :
    AffineSpace.zeroSection (ULift.{u} (Fin 1)) B ≫ s.affineSpaceToQuotientPolynomialSpec =
      s.toQuotientSpec ≫ relativeGluingMap s.ker.coequifibered_toQuotientPolynomialAlgebra
        s.ker.coequifibered_toQuotientAlgebra s.ker.quotientPolynomialEvalZero := by
  refine s.ker.isPullback_quotientPolynomialSpec.hom_ext ?_ ?_
  · rw [Category.assoc, affineSpaceToQuotientPolynomialSpec_toQuotientSpec,
      AffineSpace.zeroSection_over_assoc, Category.assoc, ← relativeGluingMap_comp,
      s.ker.polynomialC_comp_quotientPolynomialEvalZero]
    exact (Category.comp_id _).symm.trans (congrArg (s.toQuotientSpec ≫ ·)
      (relativeGluingMap_id s.ker.coequifibered_toQuotientAlgebra).symm)
  · rw [Category.assoc, affineSpaceToQuotientPolynomialSpec_toPolynomialSpec,
      ← Category.assoc (AffineSpace.zeroSection _ B), AffineSpace.zeroSection_comp_map,
      Category.assoc, Category.assoc, ← relativeGluingMap_comp,
      ← s.ker.polynomialToPolynomialZero_comp_polynomialZeroToQuotient,
      relativeGluingMap_comp V.coequifibered_toPolynomialPresheaf
        V.coequifibered_toPolynomialZeroPresheaf]
    have h : relativeGluingMap V.coequifibered_toPolynomialZeroPresheaf
        s.ker.coequifibered_toQuotientAlgebra s.ker.polynomialZeroToQuotient =
        (relativeGluingData s.ker.coequifibered_toQuotientAlgebra).toBase ≫
          inv (relativeGluingData V.coequifibered_toPolynomialZeroPresheaf).toBase := by
      rw [IsIso.eq_comp_inv]
      exact relativeGluingMap_toBase _ _ _
        s.ker.toPolynomialZeroPresheaf_comp_polynomialZeroToQuotient
    rw [reassoc_of% h, toQuotientSpec_toBase_assoc]
    change _ = s ≫ V.polynomialSpecZeroSection
    rw [
      ← polynomialSpecZeroSection_comp_polynomialSpecToAffineSpace, Category.assoc,
      IsIso.hom_inv_id, Category.comp_id]

variable {s} in
lemma normalConeZeroSection_comp_normalConeToDeformationSpace :
    s.normalConeZeroSection ≫ s.ker.normalConeToDeformationSpace =
      AffineSpace.zeroSection (ULift.{u} (Fin 1)) B ≫ s.deformationSpaceSection := by
  rw [normalConeZeroSection, deformationSpaceSection, reassoc_of%
    zeroSection_comp_affineSpaceToQuotientPolynomialSpec, Category.assoc,
    IdealSheafData.normalConeToDeformationSpace, ← relativeGluingMap_comp,
    ← relativeGluingMap_comp, s.ker.toQuotientPresheaf_comp_normalConeToQuotient]

end Construction

/-- Blueprint `prose-09-12`: Geometry of the deformation of a section

The deformation to the normal cone of a closed section `s` of a morphism `g : V ⟶ B` smooth of
pure relative dimension `d`, as data. Writing `𝔸¹_B = 𝔸(Fin 1; B)` with its zero and unit
sections `i₀`, `i₁`, the datum consists of the deformation space `𝒟_s V`, a morphism
`g̃ : 𝒟_s V ⟶ 𝔸¹_B` again smooth of relative dimension `d`, a section `s̃` of `g̃`, and the
identification of the two fibres:

```
  V ---ι₁---> 𝒟_s V <---ι₀--- N_s          B ---s---> V
  |             |              |           |          |
  g             g̃             π_N          ‖          g
  v             v              v           v          v
  B ---i₁---> 𝔸¹_B <---i₀---- B           B ---𝟙----> B
```

both squares cartesian, with `ι₁` carrying `s` to `s̃` and `ι₀` carrying `0_N` to `s̃`. Away
from `t = 0` the deformation is trivial: over the punctured line `𝔾_{m,B} ⊆ 𝔸¹_B`, the
complement of the zero section, there is a cartesian square

```
  V ×_B 𝔾_{m,B} ---κ°---> 𝒟_s V
        |                   |
       pr₂                  g̃
        v                   v
     𝔾_{m,B} -----------> 𝔸¹_B
```

identifying `g̃⁻¹(𝔾_{m,B})` with `V ×_B 𝔾_{m,B}` over `𝔾_{m,B}`, under which `s̃` is `s × 1`.

Étale-locally on `B` the deformation has coordinates (clauses (2), (4) and (5)): over a
surjective étale `v : B' ⟶ B`, an open neighbourhood of the section in the base change
`𝒟_s V ×_{𝔸¹_B} 𝔸¹_{B'}` maps étale to `𝔸^d_{𝔸¹_{B'}}` over `𝔸¹_{B'}`, carrying the section to
the zero section (`exists_etale_coordinates`).

The fibre over `t = 0` is the normal cone datum `N`.

In the purity conventions every scheme is separated of finite type over the base field, so
`g̃` and the coordinate chart are moreover separated and compactifiable, and every open
immersion is quasi-compact; this is recorded, compactifiability being what makes the dualizing
complexes defined.

Existence of the datum with `N` the normal cone of `s`
(`AlgebraicGeometry.Scheme.Hom.normalConeData`) is
`AlgebraicGeometry.Scheme.Hom.nonempty_deformationToNormalConeData`. -/
-- TODO(unify): definition-deformation-normal-bundle
structure DeformationToNormalConeData (d : ℕ) (g : V ⟶ B) (s : B ⟶ V)
    (N : NormalConeData d s) where
  /-- The deformation space `𝒟_s V`. -/
  scheme : Scheme.{u}
  /-- The structure morphism `g̃ : 𝒟_s V ⟶ 𝔸¹_B`. -/
  proj : scheme ⟶ 𝔸(ULift.{u} (Fin 1); B)
  /-- The section `s̃ : 𝔸¹_B ⟶ 𝒟_s V` of `g̃`. -/
  sect : 𝔸(ULift.{u} (Fin 1); B) ⟶ scheme
  /-- `s̃` really is a section of `g̃`. -/
  sect_comp_proj : sect ≫ proj = 𝟙 _
  /-- `g̃` is again smooth of pure relative dimension `d`. -/
  smoothOfRelativeDimension_proj : SmoothOfRelativeDimension d proj
  /-- `g̃` is separated: in the purity conventions every scheme is separated of finite type
  over the base field. -/
  isSeparated_proj : IsSeparated proj
  /-- `g̃` is compactifiable, as every separated morphism of finite type between schemes of
  finite type over a field is (Nagata). This is what makes the dualizing complex `ω_{g̃}`,
  and with it the family object of the deformation, defined. -/
  hasCompactification_proj : HasCompactification proj
  /-- The inclusion `ι₁ : V ⟶ 𝒟_s V` of the fibre over `t = 1`. -/
  oneFibre : V ⟶ scheme
  /-- The fibre of `g̃` over the unit section is `g`. -/
  isPullback_oneFibre :
    IsPullback oneFibre g proj (AffineSpace.oneSection (ULift.{u} (Fin 1)) B)
  /-- `ι₁` carries the section `s` to `s̃`. -/
  comp_oneFibre : s ≫ oneFibre = AffineSpace.oneSection (ULift.{u} (Fin 1)) B ≫ sect
  /-- The inclusion `ι₀ : N_s ⟶ 𝒟_s V` of the fibre over `t = 0`. -/
  zeroFibre : N.scheme ⟶ scheme
  /-- The fibre of `g̃` over the zero section is the normal cone. -/
  isPullback_zeroFibre :
    IsPullback zeroFibre N.proj proj (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B)
  /-- `ι₀` carries the zero section of the normal cone to `s̃`. -/
  comp_zeroFibre :
    N.zeroSection ≫ zeroFibre = AffineSpace.zeroSection (ULift.{u} (Fin 1)) B ≫ sect
  /-- The punctured line `𝔾_{m,B} ⊆ 𝔸¹_B`, as an open subscheme. -/
  puncturedLine : (𝔸(ULift.{u} (Fin 1); B)).Opens
  /-- The punctured line is the complement of the zero section. -/
  coe_puncturedLine : (puncturedLine : Set 𝔸(ULift.{u} (Fin 1); B)) =
    (Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B).base)ᶜ
  /-- The trivialisation `κ° : V ×_B 𝔾_{m,B} ⟶ 𝒟_s V` of the deformation away from `t = 0`. -/
  generic : pullback g (puncturedLine.ι ≫ 𝔸(ULift.{u} (Fin 1); B) ↘ B) ⟶ scheme
  /-- Over `𝔾_{m,B}` the deformation is `V ×_B 𝔾_{m,B}`: the square formed by `κ°`, the
  projection to `𝔾_{m,B}`, `g̃` and the inclusion `𝔾_{m,B} ⊆ 𝔸¹_B` is cartesian. -/
  isPullback_generic : IsPullback generic (pullback.snd _ _) proj puncturedLine.ι
  /-- Over `𝔾_{m,B}` the section `s̃` is `s × 1` (clause (3)): its restriction to the punctured
  line is `κ° ∘ (s × 1)`, for the section `s × 1 : 𝔾_{m,B} ⟶ V ×_B 𝔾_{m,B}`. -/
  exists_sect_generic : ∃ σ : puncturedLine.toScheme ⟶
      pullback g (puncturedLine.ι ≫ 𝔸(ULift.{u} (Fin 1); B) ↘ B),
    σ ≫ pullback.fst _ _ = (puncturedLine.ι ≫ 𝔸(ULift.{u} (Fin 1); B) ↘ B) ≫ s ∧
      σ ≫ pullback.snd _ _ = 𝟙 _ ∧ σ ≫ generic = puncturedLine.ι ≫ sect
  /-- Clauses (2), (4) and (5): étale-local coordinates on the deformation. There are a
  separated surjective étale `v : B' ⟶ B` and, writing `v₁ : 𝔸¹_{B'} ⟶ 𝔸¹_B` for its base change
  and `𝒟' = 𝒟_s V ×_{𝔸¹_B} 𝔸¹_{B'}` for the base change of the deformation (5), a quasi-compact
  open `j : W ⟶ 𝒟'` containing the base-changed section `σ` together with a quasi-compact
  étale `c : W ⟶ 𝔸^d_{𝔸¹_{B'}}` over `𝔸¹_{B'}` carrying `σ` to the zero section. Here `c` is the
  chart `u_i = x_i / t` of the deformation of the standard pair `(𝔸^d_{B'} → B', 0)`, which is
  `𝔸^d_{B'} ×_{B'} 𝔸¹_{B'}` (4), for étale coordinates `x₁, …, x_d` of `(g, s)` over `B'` (2). -/
  exists_etale_coordinates : ∃ (B' : Scheme.{u}) (v : B' ⟶ B) (W : Scheme.{u})
      (j : W ⟶ pullback proj (AffineSpace.map (ULift.{u} (Fin 1)) v))
      (c : W ⟶ 𝔸(ULift.{u} (Fin d); 𝔸(ULift.{u} (Fin 1); B')))
      (σ : 𝔸(ULift.{u} (Fin 1); B') ⟶ W),
    _root_.AlgebraicGeometry.Etale v ∧ Surjective v ∧ IsSeparated v ∧ IsOpenImmersion j ∧
      QuasiCompact j ∧ _root_.AlgebraicGeometry.Etale c ∧ QuasiCompact c ∧
      HasCompactification c ∧
      j ≫ pullback.snd _ _ =
        c ≫ 𝔸(ULift.{u} (Fin d); 𝔸(ULift.{u} (Fin 1); B')) ↘ 𝔸(ULift.{u} (Fin 1); B') ∧
      σ ≫ j ≫ pullback.fst _ _ = AffineSpace.map (ULift.{u} (Fin 1)) v ≫ sect ∧
      σ ≫ c = AffineSpace.zeroSection (ULift.{u} (Fin d)) 𝔸(ULift.{u} (Fin 1); B')

attribute [instance] DeformationToNormalConeData.smoothOfRelativeDimension_proj
  DeformationToNormalConeData.isSeparated_proj
  DeformationToNormalConeData.hasCompactification_proj

section Charts

open _root_.Polynomial

open AffineZariskiSite

variable (g : V ⟶ B) (s : B ⟶ V)

/-- The chart `Spec Γ(B, W)[t] ⟶ 𝔸¹_B` of the affine line over an affine open `W ⊆ B`. -/
noncomputable def affineLineChart {W : B.Opens} (hW : IsAffineOpen W) :
    Spec (.of Γ(B, W)[X]) ⟶ 𝔸(ULift.{u} (Fin 1); B) :=
  AffineSpace.homOfVector (Spec.map (CommRingCat.ofHom Polynomial.C) ≫ hW.fromSpec)
    fun _ ↦ (ΓSpecIso (.of Γ(B, W)[X])).inv Polynomial.X

instance {W : B.Opens} (hW : IsAffineOpen W) : IsOpenImmersion (affineLineChart hW) := by
  rw [affineLineChart, ← AffineSpace.homOfVector_map]
  have := isIso_homOfVector_specPolynomial Γ(B, W)
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- Over an affine open `U ⊆ g⁻¹ W`, the projection of the deformation space is
`Spec (Γ(W)[t] ⟶ Γ(U)[t, I(U) t⁻¹])` followed by the chart of `𝔸¹_B` over `W`. -/
lemma ι_deformationSpaceProj (U : V.AffineZariskiSite) {W : B.Opens} (hW : IsAffineOpen W)
    (hUW : U.1 ≤ g ⁻¹ᵁ W) :
    colimit.ι (relativeGluingData s.ker.coequifibered_toReesPresheaf).functor U ≫
      deformationSpaceProj g s =
      Spec.map (CommRingCat.ofHom ((s.ker.siteIdeal U).toExtendedReesAlgebra.comp
        (mapRingHom (g.appLE W U.1 hUW).hom))) ≫ affineLineChart hW := by
  refine AffineSpace.hom_ext ?_ fun i ↦ ?_
  · rw [deformationSpaceProj, Category.assoc, Category.assoc, Category.assoc,
      AffineSpace.map_over, polynomialSpecToAffineSpace_over_assoc,
      IdealSheafData.deformationSpaceToPolynomialSpec,
      relativeGluingMap_toBase_assoc _ _ _ s.ker.toPolynomialPresheaf_comp_polynomialToRees,
      ι_toBase_assoc, affineLineChart, Category.assoc, AffineSpace.homOfVector_over,
      ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp,
      ← IsAffineOpen.SpecMap_appLE_fromSpec g hW U.2 hUW,
      ← Spec.map_comp_assoc]
    congr 2
    ext x
    change _ = (s.ker.siteIdeal U).toExtendedReesAlgebra
      (Polynomial.map (g.appLE W U.1 hUW).hom (Polynomial.C x))
    rw [Polynomial.map_C]
    exact (Ideal.toExtendedReesAlgebra_C (I := s.ker.siteIdeal U) _).symm
  · rw [deformationSpaceProj, IdealSheafData.deformationSpaceToPolynomialSpec,
      ι_relativeGluingMap_assoc, ι_polynomialSpecToAffineSpace_assoc, polynomialSpecChart,
      AffineSpace.homOfVector_map, AffineSpace.comp_homOfVector,
      AffineSpace.homOfVector_appTop_coord, Function.comp_apply, affineLineChart,
      AffineSpace.comp_homOfVector, AffineSpace.homOfVector_appTop_coord, Function.comp_apply,
      ← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply,
      ← CommRingCat.comp_apply _ (Spec.map _).appTop, ← Scheme.ΓSpecIso_inv_naturality,
      CommRingCat.comp_apply]
    congr 1
    change (s.ker.siteIdeal U).toExtendedReesAlgebra Polynomial.X =
      (s.ker.siteIdeal U).toExtendedReesAlgebra (Polynomial.map _ Polynomial.X)
    rw [Polynomial.map_X]

variable {g s} in
/-- A chart of the deformation space on which `g̃` is smooth of relative dimension `d`. -/
lemma smoothOfRelativeDimension_ι_deformationSpaceProj (d : ℕ) (U : V.AffineZariskiSite)
    {W : B.Opens} (hW : IsAffineOpen W) (hUW : U.1 ≤ g ⁻¹ᵁ W)
    (h : SmoothOfRelativeDimension d (Spec.map (CommRingCat.ofHom
      ((s.ker.siteIdeal U).toExtendedReesAlgebra.comp (mapRingHom (g.appLE W U.1 hUW).hom))))) :
    SmoothOfRelativeDimension d
      (colimit.ι (relativeGluingData s.ker.coequifibered_toReesPresheaf).functor U ≫
        deformationSpaceProj g s) := by
  rw [ι_deformationSpaceProj g s U hW hUW]
  have : SmoothOfRelativeDimension (d + 0) (Spec.map (CommRingCat.ofHom
      ((s.ker.siteIdeal U).toExtendedReesAlgebra.comp (mapRingHom (g.appLE W U.1 hUW).hom))) ≫
      affineLineChart hW) := inferInstance
  rwa [add_zero] at this

/-- The standard smooth charts of `g` can be shrunk around a point of the source to basic
opens. -/
lemma exists_isStandardSmooth_appLE_basicOpen (d : ℕ) [SmoothOfRelativeDimension d g] (v : V)
    (O : V.Opens) (hvO : v ∈ O) :
    ∃ (W : B.Opens) (_ : IsAffineOpen W) (U : V.Opens) (_ : IsAffineOpen U) (_ : v ∈ U)
      (_ : U ≤ O) (hUW : U ≤ g ⁻¹ᵁ W),
      (g.appLE W U hUW).hom.IsStandardSmoothOfRelativeDimension d := by
  obtain ⟨W, hW, U₀, hU₀, hvU₀, e, hQ⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := d) (f := g) v
  obtain ⟨r, hrO, hvr⟩ := hU₀.exists_basicOpen_le (V := O) ⟨v, hvO⟩ hvU₀
  refine ⟨W, hW, V.basicOpen r, hU₀.basicOpen r, hvr, hrO, (V.basicOpen_le r).trans e, ?_⟩
  have := hU₀.isLocalization_basicOpen r
  have h := (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway
    d).right Γ(V, V.basicOpen r) r _ hQ
  rwa [RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp, Scheme.Hom.appLE_map] at h

lemma smoothOfRelativeDimension_specMap_of_isStandardSmooth {R S : CommRingCat.{u}} (d : ℕ)
    (φ : R ⟶ S) (h : φ.hom.IsStandardSmoothOfRelativeDimension d) :
    SmoothOfRelativeDimension d (Spec.map φ) := by
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension d)]
  exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ h

/-- **Charts away from the section.** Away from `s(B)` the deformation space is
`V ×_B 𝔾_{m,B}`, so `g̃` is smooth there. -/
lemma exists_chart_of_notMem_range (d : ℕ) [SmoothOfRelativeDimension d g] [IsClosedImmersion s]
    (v : V) (hv : v ∉ Set.range s) :
    ∃ U : V.AffineZariskiSite, v ∈ U.1 ∧ SmoothOfRelativeDimension d
      (colimit.ι (relativeGluingData s.ker.coequifibered_toReesPresheaf).functor U ≫
        deformationSpaceProj g s) := by
  let O : V.Opens := ⟨(Set.range s)ᶜ, s.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  obtain ⟨W, hW, U, hU, hvU, hUO, hUW, hQ⟩ := exists_isStandardSmooth_appLE_basicOpen g d v O hv
  refine ⟨⟨U, hU⟩, hvU, smoothOfRelativeDimension_ι_deformationSpaceProj d ⟨U, hU⟩ hW hUW ?_⟩
  have hI : s.ker.siteIdeal ⟨U, hU⟩ = ⊤ := by
    rw [IdealSheafData.siteIdeal, Scheme.Hom.ker_apply, Ideal.eq_top_iff_one, RingHom.mem_ker]
    have : s ⁻¹ᵁ U = ⊥ := eq_bot_iff.mpr fun b hb ↦ hUO hb ⟨b, rfl⟩
    have : Subsingleton Γ(B, s ⁻¹ᵁ U) := by
      rw [this]; infer_instance
    exact Subsingleton.elim _ _
  rw [hI]
  exact smoothOfRelativeDimension_extendedReesAlgebra_top _
    (smoothOfRelativeDimension_specMap_of_isStandardSmooth d _ hQ)

lemma basicOpen_appLE {X' Y' : Scheme.{u}} (f : X' ⟶ Y') {W : Y'.Opens} {U : X'.Opens}
    (e : U ≤ f ⁻¹ᵁ W) (r : Γ(Y', W)) :
    X'.basicOpen (f.appLE W U e r) = U ⊓ f ⁻¹ᵁ Y'.basicOpen r := by
  rw [Scheme.Hom.appLE, CommRingCat.comp_apply, Scheme.basicOpen_res, Scheme.preimage_basicOpen]

/-- **Étale coordinates along the section.** Near a point `s(b)` there are an affine open
`W ∋ b` of `B` and an affine open `U ⊆ g⁻¹ W` of `V` with `s⁻¹ U = W`, together with étale
coordinates `ψ : Γ(W)[X₁, …, X_d] ⟶ Γ(U)` over `Γ(W)` generating the ideal of the section. -/
lemma exists_etale_coordinates_of_mem_range (d : ℕ) [SmoothOfRelativeDimension d g]
    [IsClosedImmersion s] (hs : s ≫ g = 𝟙 B) (b : B) :
    ∃ (W : B.Opens) (_ : IsAffineOpen W) (U : V.AffineZariskiSite) (hUW : U.1 ≤ g ⁻¹ᵁ W),
      b ∈ W ∧ s ⁻¹ᵁ U.1 = W ∧ ∃ ψ : MvPolynomial (Fin d) Γ(B, W) →+* Γ(V, U.1), ψ.Etale ∧
        ψ.comp MvPolynomial.C = (g.appLE W U.1 hUW).hom ∧
        s.ker.siteIdeal U = (Ideal.mvPolynomialOrigin Γ(B, W) (Fin d)).map ψ := by
  have hgs : ∀ b, g (s b) = b := fun b ↦ by rw [← Scheme.Hom.comp_apply, hs]; rfl
  obtain ⟨W₀, hW₀, U₀, hU₀, hvU₀, -, hUW₀, hQ₀⟩ :=
    exists_isStandardSmooth_appLE_basicOpen g d (s b) ⊤ trivial
  have hbW₀ : b ∈ W₀ := hgs b ▸ hUW₀ hvU₀
  obtain ⟨c, hcU, hbc⟩ := hW₀.exists_basicOpen_le (V := s ⁻¹ᵁ U₀) ⟨b, hvU₀⟩ hbW₀
  set W := B.basicOpen c
  have hW : IsAffineOpen W := hW₀.basicOpen c
  set U := V.basicOpen (g.appLE W₀ U₀ hUW₀ c)
  have hU : IsAffineOpen U := hU₀.basicOpen _
  have hUW : U ≤ g ⁻¹ᵁ W := by
    rw [show U = _ from basicOpen_appLE g hUW₀ c]; exact inf_le_right
  have hsU : s ⁻¹ᵁ U = W := by
    rw [show U = _ from basicOpen_appLE g hUW₀ c, Scheme.Hom.preimage_inf,
      ← Scheme.Hom.comp_preimage, hs, Scheme.Hom.id_preimage]
    exact inf_eq_right.mpr hcU
  have hQ : (g.appLE W U hUW).hom.IsStandardSmoothOfRelativeDimension d := by
    have := hW₀.isLocalization_basicOpen c
    have := hU₀.isLocalization_basicOpen (g.appLE W₀ U₀ hUW₀ c)
    have := hW₀.appLE_eq_away_map g hU₀ hUW₀ c
    rw [this]
    exact (RingHom.isStandardSmoothOfRelativeDimension_localizationPreserves d).away _ _ _ _ hQ₀
  -- the section as a retraction of rings
  let f := g.appLE W U hUW
  let σ := s.appLE U W hsU.ge
  have hσf : σ.hom.comp f.hom = RingHom.id _ := by
    rw [← CommRingCat.hom_comp, Scheme.Hom.appLE_comp_appLE]
    rw [Scheme.Hom.appLE_congr_hom hs _ _ _ (by simp)]
    ext x
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_app, Category.id_comp]
    erw [B.presheaf.map_id]
    rfl
  obtain ⟨φ, hφf, hφ⟩ := hQ.exists_etale_mvPolynomial
  obtain ⟨a, hσa, H⟩ := exists_etale_coordinates_of_section f.hom σ.hom hσf φ hφ hφf
  have hσ : σ = s.app U ≫ B.presheaf.map (eqToHom hsU.symm).op := rfl
  have hinj : Function.Injective (B.presheaf.map (eqToHom hsU.symm).op).hom :=
    (ConcreteCategory.bijective_of_isIso _).1
  set U' := V.basicOpen a
  have hU' : IsAffineOpen U' := hU.basicOpen a
  have hU'W : U' ≤ g ⁻¹ᵁ W := (V.basicOpen_le a).trans hUW
  have := hU.isLocalization_basicOpen a
  obtain ⟨ψ, hψ, hψf, hJ⟩ := H Γ(V, U')
  refine ⟨W, hW, ⟨U', hU'⟩, hU'W, hbc, ?_, ψ, hψ, ?_, ?_⟩
  · have hb : B.basicOpen (σ a) = W := by
      rw [hσa, Scheme.basicOpen_of_isUnit _ isUnit_one]
    rw [hσ, CommRingCat.comp_apply, Scheme.basicOpen_res, ← Scheme.preimage_basicOpen] at hb
    refine le_antisymm ((s.preimage_mono (V.basicOpen_le a)).trans hsU.le) ?_
    exact hb.ge.trans inf_le_right
  · rw [hψf, RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp, Scheme.Hom.appLE_map]
  · rw [← hJ, hσ, CommRingCat.hom_comp, RingHom.ker_comp_of_injective _ hinj,
      ← Scheme.Hom.ker_apply s ⟨U, hU⟩]
    exact (s.ker.map_ideal_basicOpen ⟨U, hU⟩ a).symm

/-- **Charts along the section.** Near a point `s(b)` there are étale coordinates on `V` over `B`
in which `s` is the origin, and on the corresponding chart `g̃` is smooth. -/
lemma exists_chart_of_mem_range (d : ℕ) [SmoothOfRelativeDimension d g] [IsClosedImmersion s]
    (hs : s ≫ g = 𝟙 B) (b : B) :
    ∃ U : V.AffineZariskiSite, s b ∈ U.1 ∧ SmoothOfRelativeDimension d
      (colimit.ι (relativeGluingData s.ker.coequifibered_toReesPresheaf).functor U ≫
        deformationSpaceProj g s) := by
  obtain ⟨W, hW, U, hUW, hbW, hsU, ψ, hψ, hψf, hI⟩ :=
    exists_etale_coordinates_of_mem_range g s d hs b
  refine ⟨U, ?_, smoothOfRelativeDimension_ι_deformationSpaceProj d U hW hUW ?_⟩
  · change b ∈ s ⁻¹ᵁ U.1
    rwa [hsU]
  · rw [hI]
    exact smoothOfRelativeDimension_extendedReesAlgebra_of_etale _ _ hψ hψf

end Charts

section Smooth

open AffineZariskiSite

variable (d : ℕ) (g : V ⟶ B) [SmoothOfRelativeDimension d g] (s : B ⟶ V) [IsClosedImmersion s]

/-- Blueprint `prose-09-12` (2): the coordinates.

**The deformation space is smooth.** If `g` is smooth of relative dimension `d` with closed
section `s`, then `g̃ : D_s V ⟶ 𝔸¹_B` is smooth of relative dimension `d`: étale-locally there are
coordinates `x₁, …, x_d` on `V` over `B` in which `s` is `x_i = 0`, and on the chart
`u_i = x_i / t` the deformation space is étale over `𝔸^d × 𝔸¹` over the base. -/
theorem smoothOfRelativeDimension_deformationSpaceProj (hs : s ≫ g = 𝟙 B) :
    SmoothOfRelativeDimension d (deformationSpaceProj g s) := by
  refine smoothOfRelativeDimension_of_forall_exists_mem _ d fun x ↦ ?_
  have hex : ∃ U : V.AffineZariskiSite, s.ker.deformationSpaceProj x ∈ U.1 ∧
      SmoothOfRelativeDimension d
        (colimit.ι (relativeGluingData s.ker.coequifibered_toReesPresheaf).functor U ≫
          deformationSpaceProj g s) := by
    by_cases h : s.ker.deformationSpaceProj x ∈ Set.range s
    · obtain ⟨b, hb⟩ := h
      obtain ⟨U, hU, H⟩ := exists_chart_of_mem_range g s d hs b
      exact ⟨U, hb ▸ hU, H⟩
    · exact exists_chart_of_notMem_range g s d _ h
  obtain ⟨U, hxU, H⟩ := hex
  refine ⟨(colimit.ι (relativeGluingData s.ker.coequifibered_toReesPresheaf).functor U).opensRange,
    ?_, ?_⟩
  · rw [← toBase_preimage]
    exact hxU
  · let e := IsOpenImmersion.isoOfRangeEq
      (colimit.ι (relativeGluingData s.ker.coequifibered_toReesPresheaf).functor U)
      (colimit.ι (relativeGluingData s.ker.coequifibered_toReesPresheaf).functor U).opensRange.ι
      (by simp)
    rw [← MorphismProperty.cancel_left_of_respectsIso (P := @SmoothOfRelativeDimension d) e.hom,
      ← Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac]
    exact H

variable {g s}

/-- Blueprint `prose-09-11`: the normal cone `N_s = Spec (⨁_{r ≥ 0} I^r / I^{r+1})` of
the closed section `s` of `g`, with its projection to `B` and its zero section, as a normal cone
datum: it is smooth of relative dimension `d` over `B`, being the fibre of the smooth `g̃` over
`t = 0`. -/
noncomputable def normalConeData (hs : s ≫ g = 𝟙 B) : NormalConeData d s where
  scheme := s.ker.normalCone
  proj := normalConeProj g s
  zeroSection := s.normalConeZeroSection
  zeroSection_comp_proj := normalConeZeroSection_normalConeProj hs
  isClosedImmersion_zeroSection := inferInstance
  smoothOfRelativeDimension_proj :=
    have h := smoothOfRelativeDimension_deformationSpaceProj d g s hs
    have := smoothOfRelativeDimension_isStableUnderBaseChange (n := d)
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension d)
      (isPullback_normalConeToDeformationSpace g s) h

end Smooth

section Separated

open AffineZariskiSite

variable (g : V ⟶ B) (s : B ⟶ V)

instance : IsAffineHom s.ker.deformationSpaceToPolynomialSpec := by
  have : IsAffineHom (s.ker.deformationSpaceToPolynomialSpec ≫ V.polynomialSpecProj) := by
    rw [IdealSheafData.deformationSpaceToPolynomialSpec,
      relativeGluingMap_toBase _ _ _ s.ker.toPolynomialPresheaf_comp_polynomialToRees]
    infer_instance
  exact IsAffineHom.of_comp _ V.polynomialSpecProj

/-- `g̃` is separated if `g` is: it is affine over `𝔸¹_V`, which is a base change of `g`. -/
instance [IsSeparated g] : IsSeparated (deformationSpaceProj g s) := by
  have : IsSeparated (AffineSpace.map (ULift.{u} (Fin 1)) g) :=
    MorphismProperty.of_isPullback (P := @IsSeparated) (AffineSpace.isPullback_map g).flip ‹_›
  rw [deformationSpaceProj]
  infer_instance

instance [QuasiCompact g] : QuasiCompact (deformationSpaceProj g s) := by
  have : QuasiCompact (AffineSpace.map (ULift.{u} (Fin 1)) g) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) (AffineSpace.isPullback_map g).flip ‹_›
  rw [deformationSpaceProj]
  infer_instance

/-- `g̃` is compactifiable over a quasi-compact quasi-separated base, by Nagata's
compactification theorem. -/
lemma hasCompactification_deformationSpaceProj (d : ℕ) [SmoothOfRelativeDimension d g]
    [IsSeparated g] [QuasiCompact g] [CompactSpace B] [QuasiSeparatedSpace B]
    [IsClosedImmersion s] (hs : s ≫ g = 𝟙 B) :
    HasCompactification (deformationSpaceProj g s) :=
  have := smoothOfRelativeDimension_deformationSpaceProj d g s hs
  have := SmoothOfRelativeDimension.smooth d (deformationSpaceProj g s)
  have := QuasiCompact.compactSpace_of_compactSpace (𝔸(ULift.{u} (Fin 1); B) ↘ B)
  have := quasiSeparatedSpace_of_quasiSeparated (𝔸(ULift.{u} (Fin 1); B) ↘ B)
  (NagataCompactification (deformationSpaceProj g s)).hasCompactification

end Separated

end Scheme.Hom

end AlgebraicGeometry

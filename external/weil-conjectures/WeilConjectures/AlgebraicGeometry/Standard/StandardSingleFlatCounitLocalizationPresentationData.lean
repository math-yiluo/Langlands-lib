/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Standard.StandardSingleFlatCounitPresentation
import WeilConjectures.AlgebraicGeometry.Standard.StandardSingleBaseChangeTopRestriction

/-! # Local affine presentation data

Source: Stacks Project, Tags 0DJ9, 06YB and 0D5S.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

private theorem localizationPresentation_comp
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X X' Z : C} {T T' W : D} (e₀ : X ≅ X') (e : X' ≅ Z)
    (ε : F.obj Z ⟶ T) (t : T ≅ T') (t₀ : T' ≅ W)
    (f : F.obj X ⟶ W) (f' : F.obj X' ⟶ T')
    (h₀ : f = F.map e₀.hom ≫ f' ≫ t₀.hom)
    (he : f' = F.map e.hom ≫ ε ≫ t.hom) :
    f = F.map (e₀ ≪≫ e).hom ≫ ε ≫ (t ≪≫ t₀).hom := by
  rw [h₀, he]
  simp only [Iso.trans_hom, Functor.map_comp, Category.assoc]

private theorem localizationPresentation_flatOver_restrict
    {X Y B : Scheme.{u}} (i : X ⟶ Y) [IsOpenImmersion i] (p : Y ⟶ B)
    (M : Y.Modules) (hM : M.IsFlatOver p) : (M.restrict i).IsFlatOver (i ≫ p) := by
  intro V U e
  let U' : Y.affineOpens := ⟨i ''ᵁ U.1, U.2.image_of_isOpenImmersion i⟩
  have e' : U'.1 ≤ p ⁻¹ᵁ V.1 :=
    (i.image_mono e).trans (i.image_preimage_le (p ⁻¹ᵁ V.1))
  have hh := hM V U' e'
  have heq : (i ≫ p).appLE V.1 U.1 e ≫ (i.appIso U.1).inv =
      p.appLE V.1 U'.1 e' := by
    rw [Scheme.Hom.comp_appLE, Category.assoc, Scheme.Hom.appLE_appIso_inv]
    rfl
  convert hh using 1 <;> try rfl
  ext r m
  change (M.smul (((i.appIso U.1).inv.hom)
    (((i ≫ p).appLE V.1 U.1 e).hom r))).asHom.hom m =
      (M.smul ((p.appLE V.1 U'.1 e').hom r)).asHom.hom m
  exact congrArg (fun x ↦ (M.smul x).asHom.hom m) (congrArg (fun x ↦ x.hom r) heq)

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
/-- Concrete localized presentation witnesses used by completion.
Source: Stacks Project, Tags 0DJ9, 06YB and 0D5S.
(blueprint: lem-pc-standard-single-flat-counit-localization-presentation-data).
Proof: choose an affine open S containing g(a), then an affine open V containing a
inside the open inverse image of S. Put W = p inverse-image S. Restrict M to W
and p to W -> S. Quasi-compactness and quasi-separatedness persist under this
open base change; quasi-coherence and relative flatness restrict, since sections
on affine subopens and their scalar actions are identified by open restriction.
Apply h_affine to W -> S and V -> S, and then to the restriction of M to the top
open of W. The top-open inclusion is an isomorphism. Transport its direct image,
ordinary pullback and canonical comparison along that isomorphism, using the
unit and counit identities. This gives the displayed presentation on S, including
its bounded flat K, both identifications and their equation. Nothing is extended
from S to the whole base B. The chosen point ensures the opens are nonempty;
there is no assertion to check when A is empty. -/
theorem standardSingleFlatCounit_localization_presentation_data
    (h_affine : ∀ {Y₀ B₀ A₀ : Scheme.{u}} (p₀ : Y₀ ⟶ B₀)
      [QuasiCompact p₀] [QuasiSeparated p₀] [IsAffine B₀] [IsAffine A₀]
      (g₀ : A₀ ⟶ B₀), StandardSingleFlatCounitOnOpen p₀ g₀ ⊤)
    {Y B A : Scheme.{u}} (p : Y ⟶ B) [QuasiCompact p] [QuasiSeparated p]
    (M : Y.Modules) [M.IsQuasicoherent] (hM : M.IsFlatOver p) (g : A ⟶ B) (a : A) :
    letI := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))
    ∃ (S : B.Opens) (V : A.Opens), g a ∈ S ∧ a ∈ V ∧
      IsAffine S.toScheme ∧ IsAffine V.toScheme ∧
      ∃ hVS : V ≤ g ⁻¹ᵁ S,
        StandardSingleFlatCounitPresentation (p ∣_ S)
          (M.restrict (p ⁻¹ᵁ S).ι) (g.resLE S V hVS) := by
  let := fun X : Scheme.{u} ↦ HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))
  obtain ⟨_, ⟨S, hSaff, rfl⟩, hS, _⟩ :=
    B.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (g a)) isOpen_univ
  obtain ⟨_, ⟨V, hVaff, rfl⟩, hV, hVS⟩ :=
    A.isBasis_affineOpens.exists_subset_of_mem_open
      (show a ∈ (g ⁻¹ᵁ S : A.Opens) from hS) (g ⁻¹ᵁ S).isOpen
  let : IsAffine (Scheme.Opens.toScheme S) := hSaff
  let : IsAffine (Scheme.Opens.toScheme V) := hVaff
  refine ⟨S, V, hS, hV, hSaff, hVaff, hVS, ?_⟩
  have hflat : (M.restrict (p ⁻¹ᵁ S).ι).IsFlatOver (p ∣_ S) := by
    intro V0 U0 e
    let V1 : B.affineOpens :=
      ⟨Scheme.Opens.ι S ''ᵁ V0.1, V0.2.image_of_isOpenImmersion (Scheme.Opens.ι S)⟩
    let U1 : Y.affineOpens :=
      ⟨(p ⁻¹ᵁ S).ι ''ᵁ U0.1, U0.2.image_of_isOpenImmersion (p ⁻¹ᵁ S).ι⟩
    have e1 : U1.1 ≤ p ⁻¹ᵁ V1.1 :=
      ((p ⁻¹ᵁ S).ι.image_mono e).trans (image_morphismRestrict_preimage p S V0.1).le
    have hh := hM V1 U1 e1
    rw [morphismRestrict_appLE]
    convert hh using 1 <;> try rfl
    ext r m
    change (M.smul (((p ⁻¹ᵁ S).ι.appIso U0.1).inv.hom
      ((p.appLE V1.1 U1.1 e1).hom r))).asHom.hom m =
        (M.smul ((p.appLE V1.1 U1.1 e1).hom r)).asHom.hom m
    rw [Scheme.Opens.ι_appIso]
    rfl
  let q := p ∣_ S
  let N := M.restrict (p ⁻¹ᵁ S).ι
  let g₀ := g.resLE S V hVS
  have htop := h_affine q g₀
  have hNtop := localizationPresentation_flatOver_restrict
    (⊤ : (p ⁻¹ᵁ S).toScheme.Opens).ι q N hflat
  obtain ⟨K, hb, hf, e, t, he⟩ := htop _ hNtop
  obtain ⟨e₀, t₀, h₀⟩ := standardSingleBaseChange_topRestriction_comparison q N g₀
  refine ⟨K, hb, hf, e₀ ≪≫ e, t ≪≫ t₀, ?_⟩
  exact localizationPresentation_comp (derivedPullback g₀) e₀ e _ t t₀ _ _ h₀ he

end AlgebraicGeometry

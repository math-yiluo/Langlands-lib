/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Relative spectra of quasi-coherent algebras on the small affine Zariski site

Let `F` be a presheaf of rings on `X.AffineZariskiSite` with a coequifibered structure morphism
`α : 𝒪_X ⟶ F`, that is, a quasi-coherent `𝒪_X`-algebra. Mathlib glues the spectra `Spec F(U)`
into a scheme `(relativeGluingData H).glued` over `X`. We record its basic properties:

- `AlgebraicGeometry.Scheme.AffineZariskiSite.ι_toBase`: the chart `Spec F(U) ⟶ Spec_X F`
  over an affine open `U` lies over `Spec α(U)`;
- `AlgebraicGeometry.Scheme.AffineZariskiSite.toBase_preimage`: the preimage of `U` is the image
  of that chart, so the structure morphism is affine;
- `AlgebraicGeometry.Scheme.AffineZariskiSite.isFinite_toBase`: it is finite if every `α(U)` is;
- `AlgebraicGeometry.Scheme.AffineZariskiSite.relativeGluingMap`: a morphism of quasi-coherent
  algebras `F ⟶ G` induces a morphism `Spec_X G ⟶ Spec_X F` over `X`;
- `AlgebraicGeometry.Scheme.AffineZariskiSite.sectionsIso`: the sections of `Spec_X F` over the
  preimage of an affine open `U` are `F(U)`, compatibly with restrictions, with the structure
  morphism and with the induced morphisms.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.AffineZariskiSite

variable {X : Scheme.{u}} {F G K : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u}}
  {α : (toOpensFunctor X).op ⋙ X.presheaf ⟶ F} (H : α.Coequifibered)

instance : ((relativeGluingData H).functor ⋙ Scheme.forget).IsLocallyDirected :=
  Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma ι_toBase (U : X.AffineZariskiSite) :
    colimit.ι (relativeGluingData H).functor U ≫ (relativeGluingData H).toBase =
      Spec.map (α.app (.op U)) ≫ U.2.fromSpec :=
  colimit.ι_desc _ _

set_option backward.isDefEq.respectTransparency.types false in
lemma toBase_preimage (U : X.AffineZariskiSite) :
    (relativeGluingData H).toBase ⁻¹ᵁ U.1 =
      (colimit.ι (relativeGluingData H).functor U).opensRange := by
  simpa using! (relativeGluingData H).toBase_preimage_eq_opensRange_ι U

instance : IsAffineHom (relativeGluingData H).toBase where
  isAffine_preimage U hU := by
    rw [toBase_preimage H ⟨U, hU⟩]
    have : IsAffine ((relativeGluingData H).functor.obj ⟨U, hU⟩) :=
      inferInstanceAs (IsAffine (Spec _))
    exact isAffineOpen_opensRange _

set_option backward.isDefEq.respectTransparency false in
/-- The relative spectrum of a quasi-coherent algebra which is finite on every affine open is
finite over the base. -/
lemma isFinite_toBase (hF : ∀ U, (α.app (.op U)).hom.Finite) :
    IsFinite (relativeGluingData H).toBase := by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsFinite) _
    (iSup_affineOpens_eq_top _)]
  intro U
  let e := IsOpenImmersion.isoOfRangeEq ((relativeGluingData H).toBase ⁻¹ᵁ U).ι
    (colimit.ι (relativeGluingData H).functor ⟨U.1, U.2⟩)
    (by simpa using congr($(toBase_preimage H ⟨U.1, U.2⟩).1))
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsFinite e.inv,
    ← MorphismProperty.cancel_right_of_respectsIso @IsFinite _ U.2.isoSpec.hom]
  convert! (IsFinite.SpecMap_iff _).mpr (hF ⟨U.1, U.2⟩)
  rw [← cancel_mono U.2.fromSpec]
  simp only [IsAffineOpen.isoSpec_hom, e, Category.assoc, IsAffineOpen.toSpecΓ_fromSpec,
    morphismRestrict_ι, IsOpenImmersion.isoOfRangeEq_inv_fac_assoc]
  exact ι_toBase H _

section Map

variable {β : (toOpensFunctor X).op ⋙ X.presheaf ⟶ G} (H' : β.Coequifibered)

set_option backward.isDefEq.respectTransparency false in
/-- A morphism `φ : F ⟶ G` of quasi-coherent `𝒪_X`-algebras induces a morphism
`Spec_X G ⟶ Spec_X F` of their relative spectra over `X`. -/
noncomputable def relativeGluingMap (φ : F ⟶ G) :
    (relativeGluingData H').glued ⟶ (relativeGluingData H).glued :=
  colimit.desc _
    { pt := _
      ι.app U := Spec.map (φ.app (.op U)) ≫ colimit.ι (relativeGluingData H).functor U
      ι.naturality {U V} i := by
        dsimp [relativeGluingData]
        rw [Category.comp_id, ← Spec.map_comp_assoc, ← φ.naturality, Spec.map_comp_assoc]
        exact congrArg _ (colimit.w (relativeGluingData H).functor i) }

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma ι_relativeGluingMap (φ : F ⟶ G) (U : X.AffineZariskiSite) :
    colimit.ι (relativeGluingData H').functor U ≫ relativeGluingMap H H' φ =
      Spec.map (φ.app (.op U)) ≫ colimit.ι (relativeGluingData H).functor U :=
  colimit.ι_desc _ _

@[reassoc (attr := simp)]
lemma relativeGluingMap_toBase (φ : F ⟶ G) (hφ : α ≫ φ = β) :
    relativeGluingMap H H' φ ≫ (relativeGluingData H).toBase = (relativeGluingData H').toBase :=
  colimit.hom_ext fun U ↦ by
    rw [ι_relativeGluingMap_assoc, ι_toBase, ι_toBase, ← Spec.map_comp_assoc, ← NatTrans.comp_app,
      hφ]

lemma relativeGluingMap_id : relativeGluingMap H H (𝟙 F) = 𝟙 _ :=
  colimit.hom_ext fun U ↦ by
    rw [ι_relativeGluingMap H H (𝟙 F) U, Category.comp_id, NatTrans.id_app, Spec.map_id,
      Category.id_comp]

lemma relativeGluingMap_comp {γ : (toOpensFunctor X).op ⋙ X.presheaf ⟶ K}
    (H'' : γ.Coequifibered) (φ : F ⟶ G) (ψ : G ⟶ K) :
    relativeGluingMap H H'' (φ ≫ ψ) = relativeGluingMap H' H'' ψ ≫ relativeGluingMap H H' φ :=
  colimit.hom_ext fun U ↦ by
    rw [ι_relativeGluingMap H H'' _ U, ι_relativeGluingMap_assoc H' H'' ψ U,
      ι_relativeGluingMap H H' φ U, NatTrans.comp_app, Spec.map_comp_assoc]

lemma relativeGluingMap_preimage (φ : F ⟶ G) (hφ : α ≫ φ = β) (U : X.AffineZariskiSite) :
    relativeGluingMap H H' φ ⁻¹ᵁ (relativeGluingData H).toBase ⁻¹ᵁ U.1 =
      (relativeGluingData H').toBase ⁻¹ᵁ U.1 := by
  rw [← Scheme.Hom.comp_preimage, relativeGluingMap_toBase H H' φ hφ]

end Map

section Sections

lemma top_le_preimage_toBase (U : X.AffineZariskiSite) :
    ⊤ ≤ colimit.ι (relativeGluingData H).functor U ⁻¹ᵁ (relativeGluingData H).toBase ⁻¹ᵁ U.1 := by
  rw [toBase_preimage, Scheme.Hom.preimage_opensRange]

instance (U : X.AffineZariskiSite) :
    IsIso ((colimit.ι (relativeGluingData H).functor U).appLE _ ⊤
      (top_le_preimage_toBase H U)) := by
  rw [Scheme.Hom.appLE]
  have := Scheme.Hom.isIso_app (colimit.ι (relativeGluingData H).functor U)
    ((relativeGluingData H).toBase ⁻¹ᵁ U.1) (by rw [toBase_preimage])
  have : IsIso (homOfLE (top_le_preimage_toBase H U)).op :=
    (eqToIso (le_antisymm le_top (top_le_preimage_toBase H U)).symm).op.isIso_hom
  infer_instance

/-- The sections of the relative spectrum `Spec_X F` over the preimage of an affine open `U` of
`X` are `F(U)`. -/
noncomputable def sectionsIso (U : X.AffineZariskiSite) :
    Γ((relativeGluingData H).glued, (relativeGluingData H).toBase ⁻¹ᵁ U.1) ≅ F.obj (.op U) :=
  asIso ((colimit.ι (relativeGluingData H).functor U).appLE _ ⊤ (top_le_preimage_toBase H U)) ≪≫
    Scheme.ΓSpecIso _

lemma sectionsIso_hom (U : X.AffineZariskiSite) :
    (sectionsIso H U).hom =
      (colimit.ι (relativeGluingData H).functor U).appLE _ ⊤ (top_le_preimage_toBase H U) ≫
        (Scheme.ΓSpecIso _).hom :=
  rfl

/-- Equal morphisms of schemes induce equal maps `appLE`. -/
lemma _root_.AlgebraicGeometry.Scheme.Hom.appLE_congr_hom {X Y : Scheme.{u}} {f g : X ⟶ Y}
    (h : f = g) (U : Y.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ g ⁻¹ᵁ U) :
    f.appLE U V e = g.appLE U V e' := by
  subst h; rfl

set_option backward.isDefEq.respectTransparency false in
/-- The isomorphisms `sectionsIso` are compatible with the restriction to basic opens. -/
@[reassoc]
lemma sectionsIso_hom_naturality {U V : X.AffineZariskiSite} (i : V ⟶ U) :
    (relativeGluingData H).glued.presheaf.map
        (homOfLE ((relativeGluingData H).toBase.preimage_mono (toOpens_mono i.le))).op ≫
      (sectionsIso H V).hom = (sectionsIso H U).hom ≫ F.map i.op := by
  have hw : Spec.map (F.map i.op) ≫ colimit.ι (relativeGluingData H).functor U =
      colimit.ι (relativeGluingData H).functor V := colimit.w (relativeGluingData H).functor i
  rw [sectionsIso_hom, sectionsIso_hom, Scheme.Hom.map_appLE_assoc,
    Scheme.Hom.appLE_congr_hom hw.symm _ _ _ (by
      rw [hw]
      exact (top_le_preimage_toBase H V).trans (Scheme.Hom.preimage_mono _
        ((relativeGluingData H).toBase.preimage_mono (toOpens_mono i.le)))),
    Category.assoc]
  erw [← Scheme.ΓSpecIso_naturality]
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE_assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The isomorphisms `sectionsIso` identify the structure morphism with `α`. -/
@[reassoc]
lemma toBase_appLE_sectionsIso_hom (U : X.AffineZariskiSite) :
    (relativeGluingData H).toBase.appLE U.1 _ le_rfl ≫ (sectionsIso H U).hom = α.app (.op U) := by
  rw [sectionsIso_hom, Scheme.Hom.appLE_comp_appLE_assoc,
    Scheme.Hom.appLE_congr_hom (ι_toBase H U) _ _ _ (by simp), Scheme.Hom.comp_appLE,
    IsAffineOpen.fromSpec_app_of_le _ _ le_rfl]
  simp only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id, Category.id_comp,
    Scheme.Hom.map_appLE, Category.assoc]
  rw [show ∀ e, (Spec.map (α.app (.op U))).appLE ⊤ ⊤ e = (Spec.map (α.app (.op U))).appTop from
    fun e ↦ by simp [Scheme.Hom.appLE, Scheme.Hom.appTop]]
  erw [Scheme.ΓSpecIso_naturality]
  exact (Scheme.ΓSpecIso _).inv_hom_id_assoc _

end Sections

set_option backward.isDefEq.respectTransparency false in
/-- The isomorphisms `sectionsIso` identify the morphism induced by `φ : F ⟶ G` with `φ`. -/
@[reassoc]
lemma relativeGluingMap_appLE_sectionsIso_hom {β : (toOpensFunctor X).op ⋙ X.presheaf ⟶ G}
    (H' : β.Coequifibered) (φ : F ⟶ G) (hφ : α ≫ φ = β) (U : X.AffineZariskiSite) :
    (relativeGluingMap H H' φ).appLE _ _ (relativeGluingMap_preimage H H' φ hφ U).ge ≫
      (sectionsIso H' U).hom = (sectionsIso H U).hom ≫ φ.app (.op U) := by
  have hw := ι_relativeGluingMap H H' φ U
  rw [sectionsIso_hom, sectionsIso_hom, Scheme.Hom.appLE_comp_appLE_assoc,
    Scheme.Hom.appLE_congr_hom hw _ _ _ (by
      rw [← hw]
      exact (top_le_preimage_toBase H' U).trans (Scheme.Hom.preimage_mono _
        (relativeGluingMap_preimage H H' φ hφ U).ge)),
    Category.assoc]
  erw [← Scheme.ΓSpecIso_naturality]
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE_assoc]
  rfl

section Pullback

variable {β : (toOpensFunctor X).op ⋙ X.presheaf ⟶ G} (H' : β.Coequifibered)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma specMap_comp_natTrans_app (φ : F ⟶ G) (hφ : α ≫ φ = β) (U : X.AffineZariskiSite) :
    Spec.map (φ.app (.op U)) ≫ (relativeGluingData H).natTrans.app U =
      (relativeGluingData H').natTrans.app U := by
  change Spec.map _ ≫ (Spec.map (α.app (.op U)) ≫ (restrictIsoSpec X).inv.app U) =
    Spec.map (β.app (.op U)) ≫ (restrictIsoSpec X).inv.app U
  rw [← Spec.map_comp_assoc, ← NatTrans.comp_app, hφ]

/-- The chart of `Spec_X G` over an affine open `U` is the base change of the chart of `Spec_X F`
along the morphism induced by `φ : F ⟶ G`. -/
lemma isPullback_ι_relativeGluingMap (φ : F ⟶ G) (hφ : α ≫ φ = β) (U : X.AffineZariskiSite) :
    IsPullback (colimit.ι (relativeGluingData H').functor U) (Spec.map (φ.app (.op U)))
      (relativeGluingMap H H' φ) (colimit.ι (relativeGluingData H).functor U) := by
  refine IsPullback.of_bot ?_ (ι_relativeGluingMap H H' φ U)
    ((relativeGluingData H).isPullback_natTrans_ι_toBase U).flip
  rw [specMap_comp_natTrans_app H H' φ hφ, relativeGluingMap_toBase H H' φ hφ]
  exact ((relativeGluingData H').isPullback_natTrans_ι_toBase U).flip

/-- **Pushouts of quasi-coherent algebras give pullbacks of relative spectra.** If a commutative
square of quasi-coherent `𝒪_X`-algebras is a pushout over every affine open, the square of their
relative spectra is a pullback. -/
theorem isPullback_relativeGluingMap {F₀ F₁ F₂ F₃ : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u}}
    {α₀ : (toOpensFunctor X).op ⋙ X.presheaf ⟶ F₀} {α₁ : (toOpensFunctor X).op ⋙ X.presheaf ⟶ F₁}
    {α₂ : (toOpensFunctor X).op ⋙ X.presheaf ⟶ F₂} {α₃ : (toOpensFunctor X).op ⋙ X.presheaf ⟶ F₃}
    (H₀ : α₀.Coequifibered) (H₁ : α₁.Coequifibered) (H₂ : α₂.Coequifibered)
    (H₃ : α₃.Coequifibered) (a : F₀ ⟶ F₁) (b : F₀ ⟶ F₂) (c : F₁ ⟶ F₃) (e : F₂ ⟶ F₃)
    (hb : α₀ ≫ b = α₂) (hc : α₁ ≫ c = α₃)
    (h : ∀ U, IsPushout (a.app (.op U)) (b.app (.op U)) (c.app (.op U)) (e.app (.op U))) :
    IsPullback (relativeGluingMap H₁ H₃ c) (relativeGluingMap H₂ H₃ e)
      (relativeGluingMap H₀ H₁ a) (relativeGluingMap H₀ H₂ b) := by
  refine Scheme.isPullback_of_openCover_of_isPullback _ _ _ _ (relativeGluingData H₁).cover
    (fun U ↦ Spec (F₃.obj (.op U))) (fun U ↦ colimit.ι (relativeGluingData H₃).functor U)
    (fun U ↦ Spec.map (c.app (.op U))) (fun U ↦ isPullback_ι_relativeGluingMap H₁ H₃ c hc U)
    fun U ↦ ?_
  change IsPullback (Spec.map (c.app (.op U)))
    (colimit.ι (relativeGluingData H₃).functor U ≫ relativeGluingMap H₂ H₃ e)
    (colimit.ι (relativeGluingData H₁).functor U ≫ relativeGluingMap H₀ H₁ a) _
  rw [ι_relativeGluingMap, ι_relativeGluingMap]
  exact ((isPullback_SpecMap_of_isPushout _ _ _ _ (h U)).flip.paste_horiz
    (isPullback_ι_relativeGluingMap H₀ H₂ b hb U)).flip

end Pullback

section Local

set_option backward.isDefEq.respectTransparency false in
/-- A property of morphisms which is local on the target holds for `Spec_X F ⟶ X` as soon as it
holds for the maps `Spec F(U) ⟶ Spec Γ(X, U)`. -/
lemma toBase_of_forall (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
    (h : ∀ U : X.AffineZariskiSite, P (Spec.map (α.app (.op U)))) :
    P (relativeGluingData H).toBase := by
  refine IsZariskiLocalAtTarget.of_openCover (directedCover X) fun U ↦ ?_
  have hU := ((relativeGluingData H).isPullback_natTrans_ι_toBase U).flip
  have e : Arrow.mk ((directedCover X).pullbackHom (relativeGluingData H).toBase U) ≅
      Arrow.mk ((relativeGluingData H).natTrans.app U) :=
    Arrow.isoMk hU.isoPullback.symm (Iso.refl _) (by simp [Cover.pullbackHom])
  rw [P.arrow_mk_iso_iff e]
  change P (Spec.map (α.app (.op U)) ≫ (restrictIsoSpec X).inv.app U)
  rw [P.cancel_right_of_respectsIso]
  exact h U


set_option backward.isDefEq.respectTransparency false in
/-- A property of morphisms which is local on the target holds for the morphism of relative
spectra induced by `φ : F ⟶ G` as soon as it holds for the maps `Spec G(U) ⟶ Spec F(U)`. -/
lemma relativeGluingMap_of_forall (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
    {β : (toOpensFunctor X).op ⋙ X.presheaf ⟶ G} (H' : β.Coequifibered) (φ : F ⟶ G)
    (hφ : α ≫ φ = β) (h : ∀ U : X.AffineZariskiSite, P (Spec.map (φ.app (.op U)))) :
    P (relativeGluingMap H H' φ) := by
  refine IsZariskiLocalAtTarget.of_openCover (relativeGluingData H).cover fun U ↦ ?_
  have hU := isPullback_ι_relativeGluingMap H H' φ hφ U
  have e : Arrow.mk ((relativeGluingData H).cover.pullbackHom (relativeGluingMap H H' φ) U) ≅
      Arrow.mk (Spec.map (φ.app (.op U))) :=
    Arrow.isoMk hU.isoPullback.symm (Iso.refl _) (by
      simp only [Arrow.mk_hom, Iso.symm_hom, Iso.refl_hom, Category.comp_id, Cover.pullbackHom]
      exact hU.isoPullback_inv_snd)
  rw [P.arrow_mk_iso_iff e]
  exact h U

/-- Two opens of a relative spectrum agree if they agree on every chart `Spec F(U)`. -/
lemma opens_ext {W W' : (relativeGluingData H).glued.Opens}
    (h : ∀ U, colimit.ι (relativeGluingData H).functor U ⁻¹ᵁ W =
      colimit.ι (relativeGluingData H).functor U ⁻¹ᵁ W') : W = W' := by
  ext x
  obtain ⟨U, y, rfl⟩ := (relativeGluingData H).cover.exists_eq x
  exact congr(y ∈ $(h U))

end Local

end AlgebraicGeometry.Scheme.AffineZariskiSite

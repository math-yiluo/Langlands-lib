/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FlatBaseChangeOpenChoices
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap

/-! # Degree-zero restricted resolution section classes

Source: Stacks Project, Cohomology, Tag 01E4.
(blueprint: lem-weil-pbc-resolution-section-class-zero-augmentation).
-/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] enoughInjectives

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 2048 in
private theorem map_homologyπ
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    (S : ShortComplex C) (A : C ⥤ D) [A.PreservesZeroMorphisms]
    [A.PreservesLeftHomologyOf S] :
    (S.map A).homologyπ ≫ (S.mapHomologyIso A).hom =
      (S.mapCyclesIso A).hom ≫ A.map S.homologyπ := by
  rw [S.homologyData.left.mapHomologyIso_eq A,
    S.homologyData.left.mapCyclesIso_eq A]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc]
  rw [ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom_assoc]
  change (S.homologyData.left.map A).cyclesIso.hom ≫
      A.map S.homologyData.left.π ≫ A.map S.homologyData.left.homologyIso.inv = _
  rw [← A.map_comp, ShortComplex.LeftHomologyData.π_comp_homologyIso_inv]
  simp only [Functor.map_comp]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 2048 in
private theorem map_homologyπ_inv
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    (S : ShortComplex C) (A : C ⥤ D) [A.PreservesZeroMorphisms]
    [A.PreservesLeftHomologyOf S] :
    A.map S.homologyπ ≫ (S.mapHomologyIso A).inv =
      (S.mapCyclesIso A).inv ≫ (S.map A).homologyπ := by
  rw [← cancel_epi (S.mapCyclesIso A).hom, ← Category.assoc, ← map_homologyπ]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 2048 in
private theorem adjoint_homology_zero
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    (S : D ⥤ C) (U : C ⥤ D) [S.PreservesZeroMorphisms] [U.PreservesZeroMorphisms]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S] [PreservesFiniteLimits U]
    (adj : S ⊣ U) (K : ShortComplex C) [U.PreservesLeftHomologyOf K] :
    let L := K.map U
    adj.homEquiv _ _ ((L.mapHomologyIso S).inv ≫
        ShortComplex.homologyMap (K.mapNatTrans adj.counit)) =
      (K.mapHomologyIso U).hom := by
  let L := K.map U
  let ε := K.mapNatTrans adj.counit
  apply (cancel_epi L.homologyπ).1
  rw [← adj.homEquiv_naturality_left]
  have hc : (L.mapCyclesIso S).inv ≫ ShortComplex.cyclesMap ε =
      S.map (K.mapCyclesIso U).hom ≫ adj.counit.app K.cycles := by
    apply (cancel_mono K.iCycles).1
    change ((L.mapCyclesIso S).inv ≫ ShortComplex.cyclesMap ε) ≫ K.iCycles = _
    erw [Category.assoc, ShortComplex.cyclesMap_i]
    have hi : (L.mapCyclesIso S).inv ≫ (L.map S).iCycles = S.map L.iCycles := by
      rw [← cancel_epi (L.mapCyclesIso S).hom]
      simp only [Iso.hom_inv_id_assoc]
      exact (ShortComplex.mapCyclesIso_hom_iCycles L S).symm
    change (L.mapCyclesIso S).inv ≫ (L.map S).iCycles ≫
      adj.counit.app K.X₂ = _
    rw [← Category.assoc, hi]
    have hn := adj.counit.naturality K.iCycles
    change S.map (U.map K.iCycles) ≫ adj.counit.app K.X₂ =
      adj.counit.app K.cycles ≫ K.iCycles at hn
    rw [Category.assoc, ← hn, ← Category.assoc, ← S.map_comp,
      ShortComplex.mapCyclesIso_hom_iCycles]
  have hp := map_homologyπ L S
  have hpU := map_homologyπ K U
  have hπ : S.map L.homologyπ ≫ (L.mapHomologyIso S).inv =
      (L.mapCyclesIso S).inv ≫ (L.map S).homologyπ := by
    rw [← cancel_epi (L.mapCyclesIso S).hom, ← Category.assoc, ← hp]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, hπ, Category.assoc]
  erw [ShortComplex.homologyπ_naturality]
  rw [← Category.assoc, hc, Category.assoc]
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
  change (K.mapCyclesIso U).hom ≫
      adj.homEquiv _ K.cycles (adj.counit.app K.cycles) ≫ U.map K.homologyπ = _
  rw [adj.homEquiv_apply, adj.right_triangle_components, Category.id_comp]
  exact hpU.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 2048 in
private theorem adjoint_complex_homology_zero
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    (S : D ⥤ C) (U : C ⥤ D) [S.PreservesZeroMorphisms] [U.PreservesZeroMorphisms]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S] [PreservesFiniteLimits U]
    (adj : S ⊣ U) (K : CochainComplex C ℕ)
    [U.PreservesLeftHomologyOf (K.sc 0)] :
    adj.homEquiv _ _
      (((((U.mapHomologicalComplex (.up ℕ)).obj K).sc 0).mapHomologyIso S).inv ≫
        HomologicalComplex.homologyMap
          ((adj.counit.mapHomologicalComplex (.up ℕ)).app K) 0) =
      ((K.sc 0).mapHomologyIso U).hom := by
  exact adjoint_homology_zero S U adj (K.sc 0)

section

attribute [local irreducible] ShortComplex.mapHomologyIso ShortComplex.mapCyclesIso
  ShortComplex.homologyMap

set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
-- Avoid unfolding the concrete sheafification and homology data during this comparison.
private theorem theta_zero {Y : Scheme.{u}}
    (K : CochainComplex (SheafOfModules.{u} Y.ringCatSheaf) ℕ)
    [(SheafOfModules.forget.{u} Y.ringCatSheaf).Additive]
    [(SheafOfModules.forget.{u} Y.ringCatSheaf).PreservesLeftHomologyOf (K.sc 0)] :
    sectionCohomologyTheta K 0 =
      ((K.sc 0).mapHomologyIso (SheafOfModules.forget.{u} Y.ringCatSheaf)).hom := by
  exact @adjoint_complex_homology_zero _ _ _ _ _ _
    (PresheafOfModules.sheafification.{u} (𝟙 Y.ringCatSheaf.obj))
    (SheafOfModules.forget.{u} Y.ringCatSheaf) _ _ _ _ _
    (PresheafOfModules.sheafificationAdjunction.{u} (𝟙 Y.ringCatSheaf.obj)) K
    ‹(SheafOfModules.forget.{u} Y.ringCatSheaf).PreservesLeftHomologyOf (K.sc 0)›

end

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 2048 in
private theorem transport_homology
    {C D P Q : Type*} [Category* C] [Category* D] [Category* P] [Category* Q]
    [Abelian C] [Abelian D] [Abelian P] [Abelian Q]
    (B : C ⥤ Q) (U : D ⥤ P) (E : P ⥤ Q)
    [B.PreservesZeroMorphisms] [U.PreservesZeroMorphisms] [E.PreservesZeroMorphisms]
    [PreservesFiniteLimits E] [PreservesFiniteLimits U]
    (K : ShortComplex C) (L : ShortComplex D)
    [B.PreservesLeftHomologyOf K] [U.PreservesLeftHomologyOf L]
    [E.PreservesLeftHomologyOf
      (L.map U)]
    (a : K.map B ⟶ (L.map U).map E)
    {T : Q} (x : T ⟶ B.obj K.cycles)
    (y : T ⟶ E.obj (U.obj L.cycles))
    (h : x ≫ B.map K.iCycles ≫ a.τ₂ =
      y ≫ E.map (U.map L.iCycles)) :
    x ≫ B.map K.homologyπ ≫ (K.mapHomologyIso B).inv ≫
      ShortComplex.homologyMap a ≫
      ((L.map U).mapHomologyIso E).hom ≫
      E.map (L.mapHomologyIso U).hom =
    y ≫ E.map (U.map L.homologyπ) := by
  let N := L.map U
  have hc : x ≫ (K.mapCyclesIso B).inv ≫
      ShortComplex.cyclesMap a ≫ (N.mapCyclesIso E).hom ≫
      E.map (L.mapCyclesIso U).hom = y := by
    apply (cancel_mono (E.map (U.map L.iCycles))).1
    have hiU := congrArg E.map (ShortComplex.mapCyclesIso_hom_iCycles L U)
    simp only [Functor.map_comp] at hiU
    simp only [Category.assoc]
    erw [hiU, ShortComplex.mapCyclesIso_hom_iCycles]
    erw [ShortComplex.cyclesMap_i]
    have hiB : (K.mapCyclesIso B).inv ≫
        (K.map B).iCycles =
      B.map K.iCycles := by
      rw [← cancel_epi (K.mapCyclesIso B).hom]
      simp only [Iso.hom_inv_id_assoc]
      exact (ShortComplex.mapCyclesIso_hom_iCycles K B).symm
    rw [← Category.assoc _ _ a.τ₂]
    erw [hiB]
    exact h
  erw [reassoc_of% (map_homologyπ_inv K B)]
  erw [ShortComplex.homologyπ_naturality_assoc]
  erw [reassoc_of% (map_homologyπ N E)]
  have hpU := congrArg E.map (map_homologyπ L U)
  simp only [Functor.map_comp] at hpU
  erw [hpU]
  simpa only [Category.assoc] using congrArg
    (fun g => g ≫ E.map (U.map L.homologyπ)) hc

-- Keep the augmentation chase abstract until it is applied to sheaf and section functors.
private theorem transport_augmentation
    {C D P Q : Type*} [Category* C] [Category* D] [Category* P] [Category* Q]
    [Abelian C] [Abelian D] [Abelian P] [Abelian Q]
    (B : C ⥤ Q) (U : D ⥤ P) (E : P ⥤ Q)
    [B.PreservesZeroMorphisms] [U.PreservesZeroMorphisms] [E.PreservesZeroMorphisms]
    [PreservesFiniteLimits E] [PreservesFiniteLimits U]
    (K : ShortComplex C) (L : ShortComplex D)
    [B.PreservesLeftHomologyOf K] [U.PreservesLeftHomologyOf L]
    [E.PreservesLeftHomologyOf (L.map U)]
    (a : K.map B ⟶ (L.map U).map E)
    {R H : C} {S G : D} (r : R ⟶ H) (e : H ≅ K.homology) (x : R ⟶ K.cycles)
    (t : S ⟶ G) (d : G ≅ L.homology) (y : S ⟶ L.cycles)
    (b : B.obj R ⟶ E.obj (U.obj S))
    (θ : (L.map U).homology ⟶ U.obj L.homology)
    (hr : r ≫ e.hom = x ≫ K.homologyπ)
    (ht : t = y ≫ L.homologyπ ≫ d.inv)
    (hθ : θ = (L.mapHomologyIso U).hom)
    (ha : B.map x ≫ B.map K.iCycles ≫ a.τ₂ =
      (b ≫ E.map (U.map y)) ≫ E.map (U.map L.iCycles)) :
    B.map r ≫ B.map e.hom ≫ (K.mapHomologyIso B).inv ≫
      ShortComplex.homologyMap a ≫ ((L.map U).mapHomologyIso E).hom ≫
      E.map θ ≫ E.map (U.map d.inv) = b ≫ E.map (U.map t) := by
  rw [← B.map_comp_assoc, hr, B.map_comp_assoc, hθ, ht]
  simp only [Functor.map_comp]
  have hh := transport_homology B U E K L a (B.map x) (b ≫ E.map (U.map y)) ha
  simpa only [Category.assoc] using
    congrArg (fun g ↦ g ≫ E.map (U.map d.inv)) hh

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 2048 in
private theorem restrict_app_naturality {X : Scheme.{u}} (U : X.Opens)
    {M N : X.Modules} (a : M ⟶ N) :
    Hom.app ((restrictFunctor U.ι).map a) ⊤ ≫ (N.restrictAppIso U.ι ⊤).hom =
      (M.restrictAppIso U.ι ⊤).hom ≫ Hom.app a (U.ι ''ᵁ ⊤) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 2048 in
private theorem restricted_augmentation_sections {X : Scheme.{u}}
    {F : X.Modules} (I : InjectiveResolution F) (U : X.Opens)
    (R : RestrictedResolutionSections I U) :
    Hom.app (R.resolution.ι.f 0) ⊤ ≫ R.sections.hom.f 0 =
      (F.restrictAppIso U.ι ⊤).hom ≫
        F.presheaf.map (eqToHom U.ι_image_top.symm).op ≫ Hom.app (I.ι.f 0) U := by
  rw [R.components 0]
  rw [← Category.assoc, ← Hom.comp_app, R.augmentation]
  change Hom.app ((restrictFunctor U.ι).map (I.ι.f 0)) ⊤ ≫
      (restrictAppIso U.ι (I.cocomplex.X 0) ⊤).hom ≫
      (I.cocomplex.X 0).presheaf.map (eqToHom U.ι_image_top.symm).op = _
  have hn := (Hom.mapPresheaf (I.ι.f 0)).naturality
    (eqToHom U.ι_image_top.symm).op
  symm at hn
  change Hom.app (I.ι.f 0) (U.ι ''ᵁ ⊤) ≫
      (I.cocomplex.X 0).presheaf.map (eqToHom U.ι_image_top.symm).op =
    F.presheaf.map (eqToHom U.ι_image_top.symm).op ≫ Hom.app (I.ι.f 0) U at hn
  rw [← Category.assoc, restrict_app_naturality, Category.assoc, hn]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 2048 in
private theorem augmentation_comp_resolution
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasInjectiveResolutions C] {F : C} (I : InjectiveResolution F)
    (A : C ⥤ D) [A.Additive] :
    A.toRightDerivedZero.app F ≫ (I.isoRightDerivedObj A 0).hom =
      I.toRightDerivedZero' A ≫
        (((A.mapHomologicalComplex (.up ℕ)).obj I.cocomplex).homologyπ 0) := by
  rw [I.toRightDerivedZero_eq A]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 2048 in
/-- The class of an augmented restricted section is the direct-image augmentation
of the same section on the original open.
Source: Stacks Project, Cohomology, Tag 01E4 (lemma-describe-higher-direct-images).
(blueprint: lem-weil-pbc-resolution-section-class-zero-augmentation).

Proof: Expand the two canonical augmentations using
InjectiveResolution.toRightDerivedZero_eq. Cancel the inverse derived-resolution
comparison on the right. The augmentation equation of R and its pinned degree-zero
section component identify the section zero-cycle with the augmentation of s in I.
Naturality of the cycles-to-homology projection transports this identity to homology.
The sheafification adjunction defining sectionCohomologyTheta sends that class to
its homology-sheaf class: the counit is the identity on the original sheaf complex,
and exact sheafification commutes with its cycles and homology. Thus the section
class followed by the inverse resolution comparison is precisely the canonical
augmentation evaluated on the section identified by restrictAppIso. This argument
uses no special hypothesis on f or F and includes the empty open and zero section. -/
theorem resolutionSectionClass_zero_augmentation {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : X.Modules) (I : InjectiveResolution F) (V : Y.Opens)
    (R : RestrictedResolutionSections I (f ⁻¹ᵁ V))
    (s : ((restrictFunctor (f ⁻¹ᵁ V).ι).obj F).presheaf.obj (op ⊤)) :
    (resolutionSectionClass R.resolution
      (((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)
      V R.sections 0 ≫ Hom.app (I.isoRightDerivedObj (pushforward f) 0).inv V)
        (((RingedSpace.globalSectionsFunctor
          (f ⁻¹ᵁ V).toScheme.toRingedSpace).toRightDerivedZero.app
            ((restrictFunctor (f ⁻¹ᵁ V).ι).obj F)).hom s) =
    (Hom.app
      ((pushforward f).toRightDerivedZero.app F) V)
        (F.presheaf.map (eqToHom (f ⁻¹ᵁ V).ι_image_top.symm).op
          ((F.restrictAppIso (f ⁻¹ᵁ V).ι ⊤).hom s)) := by
  let U := f ⁻¹ᵁ V
  let A := RingedSpace.globalSectionsFunctor U.toScheme.toRingedSpace
  let B := forget₂
    (ModuleCat.{u} ((moduleRings U.toScheme.toRingedSpace).obj.obj (op ⊤)))
    AddCommGrpCat.{u}
  let D := pushforward f
  let P := SheafOfModules.forget.{u} Y.ringCatSheaf
  let E := PresheafOfModules.toPresheaf Y.ringCatSheaf.obj ⋙
    (evaluation Y.Opensᵒᵖ AddCommGrpCat.{u}).obj (op V)
  have : A.Additive := RingedSpace.globalSectionsFunctor_additive U.toScheme.toRingedSpace
  let C := (A.mapHomologicalComplex (.up ℕ)).obj R.resolution.cocomplex
  let K := (D.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  have hPA : P.Additive := inferInstanceAs
    ((SheafOfModules.forget.{u} Y.ringCatSheaf).Additive)
  have hP : P.PreservesLeftHomologyOf (K.sc 0) :=
    P.preservesLeftHomology_of_zero_f (K.sc 0) (by simp)
  let b : B.obj (A.obj ((restrictFunctor U.ι).obj F)) ⟶
      E.obj (P.obj (D.obj F)) :=
    (F.restrictAppIso U.ι ⊤).hom ≫
      F.presheaf.map (eqToHom U.ι_image_top.symm).op
  have haug : B.map (R.resolution.toRightDerivedZero' A) ≫
      B.map (C.iCycles 0) ≫ R.sections.hom.f 0 =
    (b ≫ E.map (P.map (I.toRightDerivedZero' D))) ≫
      E.map (P.map (K.iCycles 0)) := by
    have ha := congrArg B.map (R.resolution.toRightDerivedZero'_comp_iCycles A)
    simp only [Functor.map_comp] at ha
    erw [reassoc_of% ha]
    have hb := congrArg (P ⋙ E).map (I.toRightDerivedZero'_comp_iCycles D)
    simp only [Functor.map_comp, Functor.comp_map] at hb
    erw [Category.assoc, hb]
    exact restricted_augmentation_sections I U R
  have h := transport_augmentation B P E (C.sc 0) (K.sc 0)
    ((HomologicalComplex.shortComplexFunctor _ (.up ℕ) 0).map R.sections.hom)
    (A.toRightDerivedZero.app ((restrictFunctor U.ι).obj F))
    (R.resolution.isoRightDerivedObj A 0) (R.resolution.toRightDerivedZero' A)
    (D.toRightDerivedZero.app F) (I.isoRightDerivedObj D 0) (I.toRightDerivedZero' D)
    b (sectionCohomologyTheta K 0) (augmentation_comp_resolution R.resolution A)
    (I.toRightDerivedZero_eq D) (@theta_zero Y K hPA hP) haug
  have hs := ConcreteCategory.congr_hom h s
  exact hs


end AlgebraicGeometry.Scheme.Modules

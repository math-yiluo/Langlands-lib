/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SectionResolvingOplaxConstraintData
import all WeilConjectures.AlgebraicGeometry.InternalSectionTensorLocalization
import WeilConjectures.AlgebraicGeometry.SectionCochainMonoidalData
import WeilConjectures.AlgebraicGeometry.SectionRepresentativeTensorArrow

/-! # Associativity of the fixed section localization tensor map

Source: Stacks Project, sites-cohomology.tex, Tags 06YU, 0FPT, and 07A4.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option cleanup.letToHave false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.MonoidalCategory

private theorem lax_transport_monoidal
    {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D]
    {F G : C ⥤ D} [F.LaxMonoidal] (i : F ≅ G) :
    letI := Functor.LaxMonoidal.transport i
    NatTrans.IsMonoidal i.hom := by
  let := Functor.LaxMonoidal.transport i
  constructor
  · rfl
  · intro X Y
    change _ = (i.hom.app X ⊗ₘ i.hom.app Y) ≫
      (i.inv.app X ⊗ₘ i.inv.app Y) ≫ Functor.LaxMonoidal.μ F X Y ≫
        i.hom.app (X ⊗ Y)
    simp only [tensorHom_comp_tensorHom_assoc, Iso.hom_inv_id_app,
      tensorHom_id, id_whiskerRight, Category.id_comp]

private theorem lax_from_equivalence
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
    (e : C ≌ D) [e.functor.Monoidal] (H : C ⥤ E) [H.LaxMonoidal]
    (G : D ⥤ E) (k : H ≅ e.functor ⋙ G) :
    ∃ l : G.LaxMonoidal, letI := l; NatTrans.IsMonoidal k.hom := by
  let : e.inverse.Monoidal := e.inverseMonoidal
  have : e.IsMonoidal := by
    constructor
    · with_unfolding_all rfl
    · intro X Y
      with_unfolding_all rfl
  let i : e.inverse ⋙ H ≅ G :=
    Functor.isoWhiskerLeft e.inverse k ≪≫
      (Functor.associator e.inverse e.functor G).symm ≪≫
      Functor.isoWhiskerRight e.counitIso G ≪≫ Functor.leftUnitor G
  let l : G.LaxMonoidal := Functor.LaxMonoidal.transport i
  let := l
  have : NatTrans.IsMonoidal i.hom := lax_transport_monoidal i
  let j : H ≅ e.functor ⋙ G :=
    (Functor.leftUnitor H).symm ≪≫ Functor.isoWhiskerRight e.unitIso H ≪≫
      Functor.associator e.functor e.inverse H ≪≫ Functor.isoWhiskerLeft e.functor i
  have hj : NatTrans.IsMonoidal j.hom := by
    dsimp only [j, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom]
    infer_instance
  have heq : j.hom = k.hom := by
    apply NatTrans.ext
    funext X
    dsimp only [j, i, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.leftUnitor_inv_app, Functor.leftUnitor_hom_app,
      Functor.associator_hom_app, Functor.associator_inv_app]
    simp only [Category.id_comp]
    erw [k.hom.naturality_assoc]
    erw [← G.map_comp_assoc, e.functor_unit_comp, G.map_id,
      Category.id_comp, Category.comp_id]
    rfl
  refine ⟨l, ?_⟩
  rwa [heq] at hj

private theorem monoidal_change_target
    {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C]
    (m n : MonoidalCategory D) (h : m = n) (F : C ⥤ D)
    (l : @Functor.Monoidal _ _ _ _ _ n F) :
    ∃ l' : @Functor.Monoidal _ _ _ _ _ m F,
      ∀ X Y, HEq (l'.toOplaxMonoidal.δ X Y) (l.toOplaxMonoidal.δ X Y) := by
  subst n
  exact ⟨l, fun _ _ ↦ HEq.rfl⟩

private theorem tensor_eq_on_images
    {A B C : Type*} [Category* A] [Category* B] [Category* C]
    [MonoidalCategory B] [MonoidalCategory C]
    (E : A ≌ B) (q : B ⥤ C) [q.LaxMonoidal]
    (s : ∀ P Q, q.obj P ⊗ q.obj Q ⟶ q.obj (P ⊗ Q))
    (hs : ∀ {P P' Q Q'} (a : P ⟶ P') (b : Q ⟶ Q'),
      (q.map a ⊗ₘ q.map b) ≫ s P' Q' = s P Q ≫ q.map (a ⊗ₘ b))
    (hi : ∀ P Q, s (E.functor.obj P) (E.functor.obj Q) =
      Functor.LaxMonoidal.μ q (E.functor.obj P) (E.functor.obj Q))
    (P Q : B) : s P Q = Functor.LaxMonoidal.μ q P Q := by
  apply (cancel_epi
    (q.map (E.counitIso.hom.app P) ⊗ₘ q.map (E.counitIso.hom.app Q))).mp
  erw [hs (E.counitIso.hom.app P) (E.counitIso.hom.app Q),
    Functor.LaxMonoidal.μ_natural q (E.counitIso.hom.app P) (E.counitIso.hom.app Q), hi]
  rfl

namespace AlgebraicGeometry.ProEtale.ModuleRingedComparison

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)]

attribute [local implicit_reducible] tensor
  ResolvingOplaxConstraints.TensorFunctorTransport.tensorFunctor
  GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.symmetricCategory_sheaf_of_essentiallySmall
  ProEtale.sheafMonoidalCategory ProEtale.sheafBraidedCategory ProEtale.sheafSymmetricCategory
  CategoryTheory.Mod.monoidalCategory CategoryTheory.Monoidal.induced
  CategoryTheory.Mod.monoidalCategoryCochainComplex
  CategoryTheory.Mod.derivedMonoidalCategory CategoryTheory.Mod.laxMonoidalQ
  SheafOfModules.cochainModulesMonoidal RingedDerivedNative.moduleMonoidal
  ModuleObjectRingedComparison.ringedMonoidal
  ModuleObjectRingedComparison.internalComplexMonoidal
  ModuleObjectRingedComparison.sliceCochainMonoidal

attribute [local irreducible] tensorComparison qTensor totalComparison Functor.mapDerivedCategory

private theorem derived_monoidal (T : Scheme.{u}) :
    letI := ResolvingOplaxConstraints.derivedMonoidal Λ T
    ∃ m : (derivedEquivalence Λ T).functor.Monoidal, letI := m
      ∀ M N, Functor.OplaxMonoidal.δ (derivedEquivalence Λ T).functor M N =
        (tensorComparison Λ T).hom.app (M, N) := by
  have hm : ResolvingOplaxConstraints.derivedMonoidal Λ T =
      Monoidal.transport (derivedEquivalence Λ T) :=
    ResolvingOplaxConstraints.TensorFunctorTransport.monoidal_eq _
  obtain ⟨e₀, he₀, o, hη, hδ⟩ :=
    (KFlatSectionComparison.section_kflat_tensor_comparison.{u, 0, 0} Λ T).2.2.2.2.2.2.2.2
  let := Monoidal.transport (derivedEquivalence Λ T)
  let := o
  have : IsIso (Functor.OplaxMonoidal.η (derivedEquivalence Λ T).functor) := by
    change IsIso o.η
    rw [hη]
    exact ⟨⟨𝟙 _, Category.id_comp _, Category.id_comp _⟩⟩
  have (M N : DerivedCategory (internalModules Λ T)) :
      IsIso (Functor.OplaxMonoidal.δ (derivedEquivalence Λ T).functor M N) := by
    change IsIso (o.δ M N)
    rw [hδ]
    exact NatIso.hom_app_isIso (tensorComparison Λ T) (M, N)
  let mc := Functor.Monoidal.ofOplaxMonoidal (derivedEquivalence Λ T).functor
  obtain ⟨m, h⟩ := monoidal_change_target (ResolvingOplaxConstraints.derivedMonoidal Λ T)
    (Monoidal.transport (derivedEquivalence Λ T)) hm (derivedEquivalence Λ T).functor mc
  refine ⟨m, ?_⟩
  intro M N
  exact (eq_of_heq (h M N)).trans (hδ M N)

namespace ResolvingOplaxConstraints

private theorem derived_tensor_map (T : Scheme.{u})
    {M M' N N' : DerivedCategory (modules Λ T)} (a : M ⟶ M') (b : N ⟶ N') :
    (tensor Λ T).map (Prod.mkHom a b) =
      @MonoidalCategoryStruct.tensorHom _ _ (derivedMonoidal Λ T).toMonoidalCategoryStruct
        M M' N N' a b := by
  rfl

-- The comparison square specializes two large monoidal structures before cancellation.
private theorem localization_lax (T : Scheme.{u}) :
    letI := derivedMonoidal Λ T
    ∃ l : (DerivedCategory.Q (C := modules Λ T)).LaxMonoidal, letI := l
      ∀ P Q : CochainComplex (modules Λ T) ℤ,
        modelTensor Λ T P Q = Functor.LaxMonoidal.μ DerivedCategory.Q P Q := by
  let := derivedMonoidal Λ T
  obtain ⟨mc, hmc⟩ := section_cochain_monoidal_data Λ T
  let mc' : ((equivalence Λ T).mapHomologicalComplex (.up ℤ)).functor.Monoidal := by
    convert mc using 1
    all_goals with_unfolding_all rfl
  let := mc
  let := mc'
  let D := (derivedEquivalence Λ T).functor
  let qi := DerivedCategory.Q (C := internalModules Λ T)
  let qs := DerivedCategory.Q (C := modules Λ T)
  obtain ⟨m, hm⟩ := derived_monoidal Λ T
  let := m
  obtain ⟨l, hl⟩ := lax_from_equivalence
    ((equivalence Λ T).mapHomologicalComplex (.up ℤ)) (qi ⋙ D) qs (sectionLocalizationIso Λ T)
  let := l
  have := hl
  refine ⟨l, ?_⟩
  apply tensor_eq_on_images ((equivalence Λ T).mapHomologicalComplex (.up ℤ)) qs
    (modelTensor Λ T)
  · intro P P' Q Q' a b
    have hn := qTensorArrow_naturality Λ T a b
    dsimp only [qs, qTensorArrow, Functor.prod_obj, totalTensor_obj_tensor,
      modelTensor, derived_tensor_map] at hn ⊢
    convert hn using 1 <;> with_unfolding_all rfl
  · intro P Q
    have hs := ModuleObjectRingedComparison.monoidal_square qi qs
      ((equivalence Λ T).mapHomologicalComplex (.up ℤ)).functor D
      (sectionLocalizationIso Λ T) P Q
    have hn := (qTensorArrow_normalization Λ T P Q).symm
    have hθ := hm (qi.obj P) (qi.obj Q)
    have hφ := hmc P Q
    erw [hθ, hφ] at hs
    have hn' :
        (tensorComparison Λ T).hom.app (qi.obj P, qi.obj Q) ≫
          ((sectionLocalizationIso Λ T).hom.app P ⊗ₘ
            (sectionLocalizationIso Λ T).hom.app Q) ≫
          modelTensor Λ T
            (((equivalence Λ T).mapHomologicalComplex (.up ℤ)).functor.obj P)
            (((equivalence Λ T).mapHomologicalComplex (.up ℤ)).functor.obj Q) =
        D.map (Functor.LaxMonoidal.μ qi P Q) ≫
          (sectionLocalizationIso Λ T).hom.app (P ⊗ Q) ≫
          qs.map (cochainTensorComparison Λ T P Q).hom := by
      dsimp only [qi, qs, D, derived_tensor_map, modelTensor, derivedSectionFunctor,
        derivedEquivalence, Functor.asEquivalence, Functor.comp_obj,
        Functor.uncurry_obj_obj, CondensedRing.derivedTensor, curriedTensor_obj_obj,
        retainedCochainObject, Equivalence.mapHomologicalComplex,
        internalQTensorArrow, internalLocalizationTensorMap_app, internalLocalizationFunctor,
        cochainLocalizationIso, derivedSectionTensorIso, cochainSectionEquivalence,
        sectionLocalizationIso, sectionLocalizationComparison, Iso.app_hom,
        qTensorArrow] at hn ⊢
      convert hn using 1 <;> with_unfolding_all rfl
    let i := (tensorComparison Λ T).app (qi.obj P, qi.obj Q) ≪≫
      tensorIso ((sectionLocalizationIso Λ T).app P) ((sectionLocalizationIso Λ T).app Q)
    have : IsIso ((tensorComparison Λ T).hom.app (qi.obj P, qi.obj Q) ≫
        ((sectionLocalizationIso Λ T).hom.app P ⊗ₘ
          (sectionLocalizationIso Λ T).hom.app Q)) := by
      convert i.isIso_hom using 1
      all_goals with_unfolding_all rfl
    apply (cancel_epi ((tensorComparison Λ T).hom.app (qi.obj P, qi.obj Q) ≫
      ((sectionLocalizationIso Λ T).hom.app P ⊗ₘ
        (sectionLocalizationIso Λ T).hom.app Q))).mp
    convert hn'.trans hs.symm using 1
    all_goals exact Category.assoc _ _ _

/-- The specified section localization tensorator preserves the associator.

Source: Stacks Project, sites-cohomology.tex, Tags 06YU and 0FPT; the source
and target normalized associator equations in the proof of
lem-pd-section-resolving-oplax-model-edges, based on Tag 07A4.

Proof: use the already proved ordinary section monoidal data and its standard
extension to cochains. Identify its tensorator with cochainTensorComparison by
equality of the curried comparison maps and sectionTotalComparison_eq. The
ConstraintCondition in section_kflat_tensor_comparison gives the derived section
equivalence its strong monoidal structure with tensorator tensorComparison.
Transport the lax structure on internal localization followed by this equivalence
across the cochain section equivalence to section localization. The localization
factor isomorphism is monoidal by naturality and the equivalence triangle laws.
Its monoidal square and qTensorArrow_normalization have the same right side;
cancel the invertible tensorComparison and localization factors to identify
the transferred lax tensorator with qTensor on termwise internal images.
Naturality along the cochain equivalence counit and cancellation of its
invertible tensor components extend this equality to all pairs. Apply lax monoidal
associativity. No modelTensor component
is inverted, and no resolving or pullback hypothesis is used.
(auxiliary; not a blueprint node). -/
theorem section_localization_associativity (T : Scheme.{u})
    (P Q H : CochainComplex (modules Λ T) ℤ) :
    letI := derivedMonoidal Λ T
    (α_ (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)
        (DerivedCategory.Q.obj H)).hom ≫
        DerivedCategory.Q.obj P ◁ modelTensor Λ T Q H ≫ modelTensor Λ T P (Q ⊗ H) =
      modelTensor Λ T P Q ▷ DerivedCategory.Q.obj H ≫ modelTensor Λ T (P ⊗ Q) H ≫
        DerivedCategory.Q.map (α_ P Q H).hom := by
  let := derivedMonoidal Λ T
  obtain ⟨l, hl⟩ := localization_lax Λ T
  let := l
  simp only [hl]
  exact (Functor.LaxMonoidal.associativity DerivedCategory.Q P Q H).symm

end ResolvingOplaxConstraints
end AlgebraicGeometry.ProEtale.ModuleRingedComparison

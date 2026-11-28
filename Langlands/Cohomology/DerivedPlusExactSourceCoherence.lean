import Langlands.Cohomology.DerivedPlusExactSource

/-! # Identity and composition comparisons for exact bounded-below derived functors -/

noncomputable section

universe uC vC wC uD vD wD uE vE wE

namespace Langlands.Cohomology.DerivedPlusExactSource

open CategoryTheory CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
  {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{wD} D]
  {E : Type uE} [Category.{vE} E] [Abelian E] [HasDerivedCategory.{wE} E]

/-- Exact bounded-below derived image along the identity identifies with the identity. -/
def mapDerivedPlusIdIso (C : Type uC) [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C] :
    mapDerivedPlus (𝟭 C) ≅ 𝟭 (DerivedCategory.Plus C) :=
  NatIso.ofComponents
    (fun A => (DerivedCategory.Plus.ι (C := C)).preimageIso
      ((Functor.mapDerivedCategoryIdIso C).app A.obj))
    (fun {_ _} a => by
      apply (DerivedCategory.Plus.ι (C := C)).map_injective
      simp only [Functor.map_comp, Functor.preimageIso_hom, Functor.map_preimage]
      exact (Functor.mapDerivedCategoryIdIso C).hom.naturality a.hom)

private def mapComplexPlusIdIso :
    (𝟭 C).mapCochainComplexPlus ≅ 𝟭 (CochainComplex.Plus C) :=
  NatIso.ofComponents
    (fun A => (CochainComplex.Plus.ι C).preimageIso
      ((Functor.mapHomologicalComplexIdIso C (.up ℤ)).app A.obj))
    (fun {_ _} a => by
      apply (CochainComplex.Plus.ι C).map_injective
      simp only [Functor.map_comp, Functor.preimageIso_hom, Functor.map_preimage]
      exact (Functor.mapHomologicalComplexIdIso C (.up ℤ)).hom.naturality a.hom)

private theorem mapDerivedPlusIdIso_hom_Q_obj (A : CochainComplex.Plus C) :
    (mapDerivedPlusIdIso C).hom.app (DerivedCategory.Plus.Q.obj A) =
      (mapDerivedPlusFactors (𝟭 C)).hom.app A ≫
        DerivedCategory.Plus.Q.map (mapComplexPlusIdIso.hom.app A) := by
  apply (DerivedCategory.Plus.ι (C := C)).map_injective
  simp only [Functor.map_comp]
  change _ = (DerivedCategory.Plus.ι (C := C)).map ((mapDerivedPlusFactors (𝟭 C)).hom.app A) ≫
    DerivedCategory.Q.map ((CochainComplex.Plus.ι C).map (mapComplexPlusIdIso.hom.app A))
  simp only [mapDerivedPlusIdIso, mapComplexPlusIdIso, mapDerivedPlusFactors,
    NatIso.ofComponents_hom_app, Functor.preimageIso_hom, Functor.map_preimage]
  exact Functor.mapDerivedCategoryIdIso_hom_app A.obj

/-- In degree zero the single-object comparison for the identity is the derived identity
comparison. -/
theorem mapDerivedPlusIdIso_hom_single_obj (A : C) :
    (mapDerivedPlusIdIso C).hom.app ((DerivedCategory.Plus.singleFunctor C 0).obj A) =
      (mapDerivedPlusSingleIso (𝟭 C) 0).hom.app A := by
  apply (DerivedCategory.Plus.ι (C := C)).map_injective
  simp only [mapDerivedPlusIdIso, mapDerivedPlusSingleIso,
    NatIso.ofComponents_hom_app, Functor.preimageIso_hom, Functor.map_preimage]
  exact Functor.mapDerivedCategoryIdIso_hom_app_singleFunctor_obj A

variable (T : C ⥤ D) [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]
  (S : D ⥤ E) [S.Additive] [PreservesFiniteLimits S] [PreservesFiniteColimits S]

/-- The exact derived functors of two successive changes of source compose on bounded-below
objects, using the canonical comparison of the unbounded derived functors. -/
def mapDerivedPlusCompIso : mapDerivedPlus T ⋙ mapDerivedPlus S ≅ mapDerivedPlus (T ⋙ S) :=
  NatIso.ofComponents
    (fun A => (DerivedCategory.Plus.ι (C := E)).preimageIso
      ((T.mapDerivedCategoryCompIso S).app A.obj))
    (fun {_ _} a => by
      apply (DerivedCategory.Plus.ι (C := E)).map_injective
      simp only [Functor.map_comp, Functor.preimageIso_hom, Functor.map_preimage]
      exact (T.mapDerivedCategoryCompIso S).hom.naturality a.hom)

/-- Successive termwise applications to a bounded-below complex agree with the
termwise application of the composite functor. -/
def mapComplexPlusCompIso :
    T.mapCochainComplexPlus ⋙ S.mapCochainComplexPlus ≅ (T ⋙ S).mapCochainComplexPlus :=
  NatIso.ofComponents
    (fun A => (CochainComplex.Plus.ι E).preimageIso
      ((Functor.mapHomologicalComplexCompIso (Iso.refl (T ⋙ S)) (.up ℤ)).app A.obj))
    (fun {_ _} a => by
      apply (CochainComplex.Plus.ι E).map_injective
      simp only [Functor.map_comp, Functor.preimageIso_hom, Functor.map_preimage]
      exact (Functor.mapHomologicalComplexCompIso (Iso.refl (T ⋙ S)) (.up ℤ)).hom.naturality a.hom)

omit [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  [PreservesFiniteLimits T] [PreservesFiniteColimits T]
  [PreservesFiniteLimits S] [PreservesFiniteColimits S] in
private theorem mapComplexPlusCompIso_hom_hom (A : CochainComplex.Plus C) :
    ((mapComplexPlusCompIso T S).hom.app A).hom =
      (Functor.mapHomologicalComplexCompIso (Iso.refl (T ⋙ S)) (.up ℤ)).hom.app A.obj := by
  change (CochainComplex.Plus.ι E).map ((mapComplexPlusCompIso T S).hom.app A) = _
  simp only [mapComplexPlusCompIso, NatIso.ofComponents_hom_app, Functor.preimageIso_hom,
    Functor.map_preimage, Iso.app_hom]

omit [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  [PreservesFiniteLimits T] [PreservesFiniteColimits T]
  [PreservesFiniteLimits S] [PreservesFiniteColimits S] in
private theorem mapComplexPlusCompIso_inv_hom (A : CochainComplex.Plus C) :
    ((mapComplexPlusCompIso T S).inv.app A).hom =
      (Functor.mapHomologicalComplexCompIso (Iso.refl (T ⋙ S)) (.up ℤ)).inv.app A.obj := by
  change (CochainComplex.Plus.ι E).map ((mapComplexPlusCompIso T S).inv.app A) = _
  simp only [mapComplexPlusCompIso, NatIso.ofComponents_inv_app, Functor.preimageIso_inv,
    Functor.map_preimage, Iso.app_inv]

/-- On a complex representative, the exact derived composition comparison is the
termwise composition comparison transported by localization. -/
theorem mapDerivedPlusCompIso_hom_Q_obj (A : CochainComplex.Plus C) :
    (mapDerivedPlusCompIso T S).hom.app (DerivedCategory.Plus.Q.obj A) =
      (mapDerivedPlus S).map ((mapDerivedPlusFactors T).hom.app A) ≫
        (mapDerivedPlusFactors S).hom.app (T.mapCochainComplexPlus.obj A) ≫
        DerivedCategory.Plus.Q.map ((mapComplexPlusCompIso T S).hom.app A) ≫
        (mapDerivedPlusFactors (T ⋙ S)).inv.app A := by
  apply (DerivedCategory.Plus.ι (C := E)).map_injective
  simp only [Functor.map_comp]
  change _ = S.mapDerivedCategory.map
      ((DerivedCategory.Plus.ι (C := D)).map ((mapDerivedPlusFactors T).hom.app A)) ≫
    (DerivedCategory.Plus.ι (C := E)).map
      ((mapDerivedPlusFactors S).hom.app (T.mapCochainComplexPlus.obj A)) ≫
    DerivedCategory.Q.map ((CochainComplex.Plus.ι E).map ((mapComplexPlusCompIso T S).hom.app A)) ≫
    (DerivedCategory.Plus.ι (C := E)).map ((mapDerivedPlusFactors (T ⋙ S)).inv.app A)
  simp only [mapDerivedPlusCompIso, mapComplexPlusCompIso, mapDerivedPlusFactors,
    NatIso.ofComponents_hom_app, NatIso.ofComponents_inv_app,
    Functor.preimageIso_hom, Functor.preimageIso_inv, Functor.map_preimage]
  exact T.mapDerivedCategoryCompIso_hom_app_Q_obj S A.obj

/-- The composition comparison agrees with the single-complex identifications on a
coefficient object. -/
@[reassoc]
theorem mapDerivedPlusCompIso_hom_single_obj (A : C) (n : ℤ) :
    (mapDerivedPlusCompIso T S).hom.app ((DerivedCategory.Plus.singleFunctor C n).obj A) ≫
        (mapDerivedPlusSingleIso (T ⋙ S) n).hom.app A =
      (mapDerivedPlus S).map ((mapDerivedPlusSingleIso T n).hom.app A) ≫
        (mapDerivedPlusSingleIso S n).hom.app (T.obj A) := by
  apply (DerivedCategory.Plus.ι (C := E)).map_injective
  simp only [Functor.map_comp]
  change _ = S.mapDerivedCategory.map
      ((DerivedCategory.Plus.ι (C := D)).map ((mapDerivedPlusSingleIso T n).hom.app A)) ≫
    (DerivedCategory.Plus.ι (C := E)).map ((mapDerivedPlusSingleIso S n).hom.app (T.obj A))
  simp only [mapDerivedPlusCompIso, mapDerivedPlusSingleIso,
    NatIso.ofComponents_hom_app, Functor.preimageIso_hom, Functor.map_preimage]
  exact T.mapDerivedCategoryCompIso_hom_app_comp_mapDerivedCategorySingleFunctor_hom_app S A n

private theorem mapDerivedPlusCompIso_factors_inv (A : CochainComplex.Plus C) :
    (mapDerivedPlusFactors S).inv.app (T.mapCochainComplexPlus.obj A) ≫
        (mapDerivedPlus S).map ((mapDerivedPlusFactors T).inv.app A) ≫
        (mapDerivedPlusCompIso T S).hom.app (DerivedCategory.Plus.Q.obj A) =
      DerivedCategory.Plus.Q.map ((mapComplexPlusCompIso T S).hom.app A) ≫
        (mapDerivedPlusFactors (T ⋙ S)).inv.app A := by
  rw [mapDerivedPlusCompIso_hom_Q_obj]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  have h := (mapDerivedPlus S).map_id (DerivedCategory.Plus.Q.obj (T.mapCochainComplexPlus.obj A))
  erw [h]
  simp only [Category.id_comp, Iso.inv_hom_id_app_assoc]

universe uB vB wB

variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
  [EnoughInjectives C] [EnoughInjectives D] [EnoughInjectives E]
  (F : C ⥤ B) [F.Additive] (G : D ⥤ B) [G.Additive] (H : E ⥤ B) [H.Additive]
  (α : F ⟶ T ⋙ G) (β : G ⟶ S ⋙ H)

omit [EnoughInjectives C] in
private theorem comparisonUnit_app (A : CochainComplex.Plus C) :
    (comparisonUnit T F G α).app A =
      DerivedCategory.Plus.Q.map
        (α.mapCochainComplexPlus.app A ≫ (mapComplexPlusCompIso T G).inv.app A) ≫
      G.rightDerivedFunctorPlusUnit.app (T.mapCochainComplexPlus.obj A) ≫
      G.rightDerivedFunctorPlus.map ((mapDerivedPlusFactors T).inv.app A) := by
  simp only [comparisonUnit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id]
  rfl

omit [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E] [HasDerivedCategory B]
  [EnoughInjectives C] [EnoughInjectives D] [EnoughInjectives E]
  [PreservesFiniteLimits T] [PreservesFiniteColimits T]
  [PreservesFiniteLimits S] [PreservesFiniteColimits S] in
private theorem termwiseComparison_comp (A : CochainComplex.Plus C) :
    α.mapCochainComplexPlus.app A ≫ (mapComplexPlusCompIso T G).inv.app A ≫
        β.mapCochainComplexPlus.app (T.mapCochainComplexPlus.obj A) ≫
        (mapComplexPlusCompIso S H).inv.app (T.mapCochainComplexPlus.obj A) ≫
        H.mapCochainComplexPlus.map ((mapComplexPlusCompIso T S).hom.app A) =
      (α ≫ Functor.whiskerLeft T β).mapCochainComplexPlus.app A ≫
        (mapComplexPlusCompIso (T ⋙ S) H).inv.app A := by
  apply (CochainComplex.Plus.ι B).map_injective
  simp only [CochainComplex.Plus.ι, ObjectProperty.ι_map]
  ext n
  simp only [ObjectProperty.FullSubcategory.comp_hom, HomologicalComplex.comp_f,
    NatTrans.mapCochainComplexPlus_app_hom, Functor.mapCochainComplexPlus_map_hom,
    mapComplexPlusCompIso_hom_hom, mapComplexPlusCompIso_inv_hom, NatTrans.mapHomologicalComplex_app_f,
    Functor.mapHomologicalComplexCompIso_hom_app_f, Functor.mapHomologicalComplexCompIso_inv_app_f,
    Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, Functor.mapHomologicalComplex_map_f,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.mapCochainComplexPlus_obj_obj]
  dsimp only [Functor.comp_obj, Functor.mapHomologicalComplex_obj_X]
  simp only [H.map_id, Category.comp_id, Category.id_comp]

/-- Right-derived comparisons along successive exact functors agree with the comparison
of the composite termwise maps. -/
theorem rightDerivedComparison_comp :
    rightDerivedComparison T F G α ≫
        Functor.whiskerLeft (mapDerivedPlus T) (rightDerivedComparison S G H β) ≫
        Functor.whiskerRight (mapDerivedPlusCompIso T S).hom H.rightDerivedFunctorPlus =
      rightDerivedComparison (T ⋙ S) F H (α ≫ Functor.whiskerLeft T β) := by
  apply F.rightDerivedFunctorPlus.rightDerived_ext F.rightDerivedFunctorPlusUnit
    (CochainComplex.Plus.quasiIso C)
  apply NatTrans.ext
  funext A
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.comp_obj,
    rightDerivedComparison_fac_assoc, rightDerivedComparison_fac, comparisonUnit_app, Category.assoc]
  rw [(rightDerivedComparison S G H β).naturality_assoc,
    rightDerivedComparison_fac_assoc, comparisonUnit_app]
  simp only [Functor.comp_map, Category.assoc]
  rw [← H.rightDerivedFunctorPlus.map_comp, ← H.rightDerivedFunctorPlus.map_comp,
    mapDerivedPlusCompIso_factors_inv, H.rightDerivedFunctorPlus.map_comp]
  erw [← (H.rightDerivedFunctorPlusUnit).naturality_assoc ((mapComplexPlusCompIso T S).hom.app A)]
  simp only [Functor.comp_map, ← Functor.map_comp_assoc]
  simp only [Category.assoc, termwiseComparison_comp]

/-- The composition law evaluated on degree-zero coefficient complexes. -/
theorem derivedComplexComparison_comp :
    derivedComplexComparison T F G α ≫
        Functor.whiskerLeft T (derivedComplexComparison S G H β) =
      derivedComplexComparison (T ⋙ S) F H (α ≫ Functor.whiskerLeft T β) := by
  apply NatTrans.ext
  funext A
  simp only [derivedComplexComparison, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc]
  erw [(rightDerivedComparison S G H β).naturality_assoc ((mapDerivedPlusSingleIso T 0).hom.app A)]
  simp only [Functor.comp_map, ← Functor.map_comp,
    ← mapDerivedPlusCompIso_hom_single_obj]
  simp only [Functor.map_comp]
  have h := congrArg (fun t => t.app ((DerivedCategory.Plus.singleFunctor C 0).obj A))
    (rightDerivedComparison_comp T S F G H α β)
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.assoc, Functor.comp_obj, DerivedPlus.derivedComplex] using congrArg
      (fun t => t ≫ H.rightDerivedFunctorPlus.map ((mapDerivedPlusSingleIso (T ⋙ S) 0).hom.app A)) h

omit [HasDerivedCategory C] [HasDerivedCategory B] [EnoughInjectives C] in
private theorem termwiseComparison_id (A : CochainComplex.Plus C) :
    (Functor.leftUnitor F).inv.mapCochainComplexPlus.app A ≫
        (mapComplexPlusCompIso (𝟭 C) F).inv.app A ≫
        F.mapCochainComplexPlus.map (mapComplexPlusIdIso.hom.app A) =
      𝟙 (F.mapCochainComplexPlus.obj A) := by
  have h : (mapComplexPlusIdIso.hom.app A).hom =
      (Functor.mapHomologicalComplexIdIso C (.up ℤ)).hom.app A.obj := by
    change (CochainComplex.Plus.ι C).map (mapComplexPlusIdIso.hom.app A) = _
    simp only [mapComplexPlusIdIso, NatIso.ofComponents_hom_app, Functor.preimageIso_hom,
      Functor.map_preimage, Iso.app_hom]
  apply (CochainComplex.Plus.ι B).map_injective
  simp only [CochainComplex.Plus.ι, ObjectProperty.ι_map]
  ext n
  simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.id_hom,
    HomologicalComplex.comp_f, HomologicalComplex.id_f, NatTrans.mapCochainComplexPlus_app_hom,
    Functor.mapCochainComplexPlus_map_hom, mapComplexPlusCompIso_inv_hom, h,
    NatTrans.mapHomologicalComplex_app_f, Functor.leftUnitor_inv_app,
    Functor.mapHomologicalComplexCompIso_inv_app_f, Iso.refl_inv, NatTrans.id_app,
    Functor.mapHomologicalComplex_map_f, Functor.mapHomologicalComplexIdIso_hom_app_f]
  dsimp only [Functor.comp_obj, Functor.id_obj, Functor.mapCochainComplexPlus_obj_obj,
    Functor.mapHomologicalComplex_obj_X]
  simp only [F.map_id, Category.id_comp]

/-- The derived comparison for the identity source change reduces to the natural unit
identification. -/
theorem rightDerivedComparison_id :
    rightDerivedComparison (𝟭 C) F F (Functor.leftUnitor F).inv ≫
        Functor.whiskerRight (mapDerivedPlusIdIso C).hom F.rightDerivedFunctorPlus =
      (Functor.leftUnitor F.rightDerivedFunctorPlus).inv := by
  apply F.rightDerivedFunctorPlus.rightDerived_ext F.rightDerivedFunctorPlusUnit
    (CochainComplex.Plus.quasiIso C)
  apply NatTrans.ext
  funext A
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    rightDerivedComparison_fac_assoc, comparisonUnit_app, Functor.leftUnitor_inv_app, Category.assoc]
  rw [← F.rightDerivedFunctorPlus.map_comp, mapDerivedPlusIdIso_hom_Q_obj,
    Iso.inv_hom_id_app_assoc]
  erw [← F.rightDerivedFunctorPlusUnit.naturality (mapComplexPlusIdIso.hom.app A)]
  simp only [Functor.comp_map, ← Functor.map_comp_assoc, Category.assoc, termwiseComparison_id]
  have h := (DerivedCategory.Plus.Q (C := B)).map_id (F.mapCochainComplexPlus.obj A)
  erw [h, Category.id_comp, Category.comp_id]
  rfl

/-- The induced comparison on degree-zero coefficients has the identity law. -/
theorem derivedComplexComparison_id :
    derivedComplexComparison (𝟭 C) F F (Functor.leftUnitor F).inv =
      (Functor.leftUnitor (DerivedPlus.derivedComplex F)).inv := by
  apply NatTrans.ext
  funext A
  simp only [derivedComplexComparison, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, ← mapDerivedPlusIdIso_hom_single_obj,
    Functor.leftUnitor_inv_app]
  have h := congrArg (fun t => t.app ((DerivedCategory.Plus.singleFunctor C 0).obj A))
    (rightDerivedComparison_id F)
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.leftUnitor_inv_app,
    DerivedPlus.derivedComplex, Functor.comp_obj] using h

end Langlands.Cohomology.DerivedPlusExactSource

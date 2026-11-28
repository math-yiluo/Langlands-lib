import Langlands.Cohomology.DerivedPlusExactSource

/-! # Bounded-below right derivation after an exact functor preserving injectives -/

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
  [EnoughInjectives C] [EnoughInjectives D]
  (T : C ⥤ D) [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]
  (G : D ⥤ E) [G.Additive]

/-- A comparison through an exact functor factors through the right derivation of the
original transformation followed by the comparison for the identity. -/
theorem rightDerivedComparison_factor (F : C ⥤ E) [F.Additive] (τ : F ⟶ T ⋙ G) :
    rightDerivedComparison T F G τ =
      τ.rightDerivedFunctorPlus ≫ rightDerivedComparison T (T ⋙ G) G (𝟙 _) := by
  apply Functor.rightDerived_ext _ F.rightDerivedFunctorPlusUnit (CochainComplex.Plus.quasiIso C)
  apply NatTrans.ext
  funext A
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, rightDerivedComparison_fac,
    NatTrans.rightDerivedFunctorPlus_fac_app_assoc]
  simp only [comparisonUnit, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, NatTrans.mapCochainComplexPlus_id,
    Category.id_comp, Category.comp_id, Functor.map_comp, Category.assoc]

variable [T.PreservesInjectiveObjects]

private def onInjectives : InjectiveObject C ⥤ InjectiveObject D :=
  ObjectProperty.lift _ (InjectiveObject.ι C ⋙ T) (fun J => T.injective_obj_of_injective J.property)

private instance onInjectives_additive : (onInjectives T).Additive := by
  dsimp only [onInjectives]
  infer_instance

omit [EnoughInjectives C] in
private theorem isIso_compositeUnit (A : CochainComplex.Plus (InjectiveObject C)) :
    IsIso ((comparisonUnit T (T ⋙ G) G (𝟙 _)).app
      ((InjectiveObject.ι C).mapCochainComplexPlus.obj A)) := by
  have : IsIso (G.rightDerivedFunctorPlusUnit.app
      (T.mapCochainComplexPlus.obj ((InjectiveObject.ι C).mapCochainComplexPlus.obj A))) := by
    change IsIso (G.rightDerivedFunctorPlusUnit.app ((InjectiveObject.ι D).mapCochainComplexPlus.obj
      ((onInjectives T).mapCochainComplexPlus.obj A)))
    infer_instance
  simp only [comparisonUnit, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, NatTrans.mapCochainComplexPlus_id,
    Category.id_comp, Category.comp_id]
  infer_instance

private theorem isIso_rightDerivedComparison_id :
    IsIso (rightDerivedComparison T (T ⋙ G) G (𝟙 _)) := by
  apply ((CochainComplex.Plus.localizerMorphism C).isIso_iff_of_hasRightResolutions
    DerivedCategory.Plus.Q _).mpr
  intro A
  let B := (InjectiveObject.ι C).mapCochainComplexPlus.obj A
  change IsIso ((rightDerivedComparison T (T ⋙ G) G (𝟙 _)).app (DerivedCategory.Plus.Q.obj B))
  have : IsIso ((T ⋙ G).rightDerivedFunctorPlusUnit.app B) := inferInstance
  have : IsIso ((T ⋙ G).rightDerivedFunctorPlusUnit.app B ≫
      (rightDerivedComparison T (T ⋙ G) G (𝟙 _)).app (DerivedCategory.Plus.Q.obj B)) := by
    rw [rightDerivedComparison_fac]
    exact isIso_compositeUnit T G A
  exact IsIso.of_isIso_comp_left ((T ⋙ G).rightDerivedFunctorPlusUnit.app B) _

/-- For an exact functor preserving injectives the identity comparison is invertible on the
bounded-below derived category. -/
def rightDerivedCompIso :
    (T ⋙ G).rightDerivedFunctorPlus ≅ mapDerivedPlus T ⋙ G.rightDerivedFunctorPlus := by
  letI := isIso_rightDerivedComparison_id T G
  exact asIso (rightDerivedComparison T (T ⋙ G) G (𝟙 _))

/-- The composition isomorphism on coefficient objects, placed in degree zero. -/
def derivedComplexCompIso : DerivedPlus.derivedComplex (T ⋙ G) ≅ T ⋙ DerivedPlus.derivedComplex G :=
  Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor C 0) (rightDerivedCompIso T G) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (mapDerivedPlusSingleIso T 0) _ ≪≫
    Functor.associator _ _ _

/-- The comparison on coefficient objects factors through the derived transformation and the
composition isomorphism. -/
theorem derivedComplexComparison_factor (F : C ⥤ E) [F.Additive] (τ : F ⟶ T ⋙ G) :
    derivedComplexComparison T F G τ =
      Functor.whiskerLeft (DerivedCategory.Plus.singleFunctor C 0) τ.rightDerivedFunctorPlus ≫
        (derivedComplexCompIso T G).hom := by
  simp only [derivedComplexComparison, derivedComplexCompIso, rightDerivedCompIso,
    asIso_hom, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    rightDerivedComparison_factor T G F τ, Functor.whiskerLeft_comp, Category.assoc]

end Langlands.Cohomology.DerivedPlusExactSource

import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Commuting squares of exact functors on actual derived categories -/

noncomputable section

universe wA wB wC wD

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits

variable {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory.{wA} A]
variable {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory.{wB} B]
variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory.{wC} C]
variable {D : Type*} [Category* D] [Abelian D] [HasDerivedCategory.{wD} D]
variable (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
variable (G : A ⥤ C) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
variable (R : B ⥤ D) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
variable (S : C ⥤ D) [S.Additive] [PreservesFiniteLimits S] [PreservesFiniteColimits S]

/-- Descend an actual comparison of exact composites, with the chosen derived
localization universe of each of the four categories independent. -/
def exactDerivedSquareIso (e : F ⋙ R ≅ G ⋙ S) :
    F.mapDerivedCategory ⋙ R.mapDerivedCategory ≅
      G.mapDerivedCategory ⋙ S.mapDerivedCategory :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
    (F.mapHomologicalComplex _ ⋙ R.mapHomologicalComplex _ ⋙ DerivedCategory.Q)
    (G.mapHomologicalComplex _ ⋙ S.mapHomologicalComplex _ ⋙ DerivedCategory.Q) _ _
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ) ≪≫
          (Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ S)) (ComplexShape.up ℤ)).symm)
        DerivedCategory.Q ≪≫ Functor.associator _ _ _)

instance (e : F ⋙ R ≅ G ⋙ S) :
    NatTrans.CommShift (exactDerivedSquareIso F G R S e).hom ℤ := by
  apply +allowSynthFailures NatTrans.CommShift.liftNatTrans
  change NatTrans.CommShift
    ((Functor.associator (F.mapHomologicalComplex _) (R.mapHomologicalComplex _)
        DerivedCategory.Q).inv ≫
      Functor.whiskerRight
        ((Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)).hom ≫
          (Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ S))
            (ComplexShape.up ℤ)).inv) DerivedCategory.Q ≫
      (Functor.associator (G.mapHomologicalComplex _) (S.mapHomologicalComplex _)
        DerivedCategory.Q).hom) ℤ
  infer_instance

/-- Recovery on a cochain representative uses the actual termwise comparison,
conjugated by the two composite factorization isomorphisms. -/
@[reassoc] theorem exactDerivedSquareIso_hom_app_Q_obj
    (e : F ⋙ R ≅ G ⋙ S) (K : CochainComplex A ℤ) :
    (exactDerivedSquareIso F G R S e).hom.app (DerivedCategory.Q.obj K) =
      R.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
        R.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex _).obj K) ≫
        DerivedCategory.Q.map ((e.hom.mapHomologicalComplex (ComplexShape.up ℤ)).app K) ≫
        S.mapDerivedCategoryFactors.inv.app ((G.mapHomologicalComplex _).obj K) ≫
        S.mapDerivedCategory.map (G.mapDerivedCategoryFactors.inv.app K) := by
  exact (Localization.liftNatTrans_app ..).trans (by
    simp [Localization.Lifting.iso, Functor.mapHomologicalComplexCompIso,
      NatIso.mapHomologicalComplex, Functor.comp_obj, Category.assoc]
    erw [Category.id_comp])

/-- Single-degree objects recover the original square, with the canonical
single-degree comparisons for both exact composites. -/
@[reassoc] theorem exactDerivedSquareIso_hom_app_single
    (e : F ⋙ R ≅ G ⋙ S) (M : A) (q : ℤ) :
    (exactDerivedSquareIso F G R S e).hom.app
        ((DerivedCategory.singleFunctor A q).obj M) =
      R.mapDerivedCategory.map ((F.mapDerivedCategorySingleFunctor q).hom.app M) ≫
        (R.mapDerivedCategorySingleFunctor q).hom.app (F.obj M) ≫
        (DerivedCategory.singleFunctor D q).map (e.hom.app M) ≫
        (S.mapDerivedCategorySingleFunctor q).inv.app (G.obj M) ≫
        S.mapDerivedCategory.map ((G.mapDerivedCategorySingleFunctor q).inv.app M) := by
  simp [← DerivedCategory.Q_obj_single_obj, exactDerivedSquareIso_hom_app_Q_obj,
    Functor.mapDerivedCategorySingleFunctor_hom_app,
    Functor.mapDerivedCategorySingleFunctor_inv_app,
    DerivedCategory.singleFunctorIsoCompQ_hom_app,
    DerivedCategory.singleFunctorIsoCompQ_inv_app,
    HomologicalComplex.natTransMapHomologicalComplex_app_single_obj,
    HomologicalComplex.singleMapHomologicalComplex_comp_hom_app,
    HomologicalComplex.singleMapHomologicalComplex_comp_inv_app,
    Functor.map_comp, Category.assoc]
  dsimp only [CochainComplex.singleFunctor]
  simp only [R.mapDerivedCategoryFactors_hom_naturality_assoc,
    dsimp% S.mapDerivedCategoryFactors.inv.naturality_assoc
      ((HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℤ) q).inv.app M),
    Functor.mapHomologicalComplexCompIso, NatIso.mapHomologicalComplex,
    Iso.refl_inv, NatTrans.mapHomologicalComplex_id, NatTrans.id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]

variable (F' : A ⥤ B) [F'.Additive] [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
variable (G' : A ⥤ C) [G'.Additive] [PreservesFiniteLimits G'] [PreservesFiniteColimits G']

/-- A commuting comparison of ordinary exact squares remains commuting after
localization on all derived objects and morphisms. -/
@[reassoc] theorem exactDerivedSquareIso_naturality
    (e : F ⋙ R ≅ G ⋙ S) (e' : F' ⋙ R ≅ G' ⋙ S)
    (a : F ⟶ F') (b : G ⟶ G')
    (h : Functor.whiskerRight a R ≫ e'.hom =
      e.hom ≫ Functor.whiskerRight b S) :
    Functor.whiskerRight a.mapDerivedCategory R.mapDerivedCategory ≫
        (exactDerivedSquareIso F' G' R S e').hom =
      (exactDerivedSquareIso F G R S e).hom ≫
        Functor.whiskerRight b.mapDerivedCategory S.mapDerivedCategory := by
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
  intro K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app,
    NatTrans.mapDerivedCategory_app_Q_obj, exactDerivedSquareIso_hom_app_Q_obj,
    Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app_assoc,
    Iso.inv_hom_id_app]
  simp only [Functor.map_comp, Category.assoc]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [R.mapDerivedCategoryFactors_hom_naturality_assoc,
    ← dsimp% S.mapDerivedCategoryFactors.inv.naturality_assoc
      ((b.mapHomologicalComplex (ComplexShape.up ℤ)).app K)]
  have hc :
      (R.mapHomologicalComplex _).map ((a.mapHomologicalComplex _).app K) ≫
          (e'.hom.mapHomologicalComplex _).app K =
        (e.hom.mapHomologicalComplex _).app K ≫
          (S.mapHomologicalComplex _).map ((b.mapHomologicalComplex _).app K) := by
    ext q
    exact congr_app h (K.X q)
  rw [← DerivedCategory.Q.map_comp_assoc, hc, DerivedCategory.Q.map_comp_assoc]

end Langlands.Cohomology

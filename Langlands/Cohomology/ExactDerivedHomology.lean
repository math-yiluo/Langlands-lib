import Langlands.Cohomology.DivisibleSystem.InverseLimit
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! # Homology of an exact functor on derived categories -/

noncomputable section

universe uC vC wC uD vD wD

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits

variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable {D : Type uD} [Category.{vD} D] [Abelian D]
variable [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]
variable (F : C ⥤ D) [F.Additive]
variable [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- On complex representatives, derived homology of the exact image is the
exact image of derived homology, through the canonical localization comparisons. -/
def exactDerivedHomologyIsoOnComplexes (q : ℤ) :
    DerivedCategory.Q ⋙ (F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor D q) ≅
      DerivedCategory.Q ⋙ (DerivedCategory.homologyFunctor C q ⋙ F) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight F.mapDerivedCategoryFactors _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (DerivedCategory.homologyFunctorFactors D q) ≪≫
    mapHomologicalComplexHomologyIso F (ComplexShape.up ℤ) q ≪≫
    (Functor.isoWhiskerRight (DerivedCategory.homologyFunctorFactors C q) F).symm ≪≫
    Functor.associator _ _ _

/-- An exact functor on abelian categories commutes with homology on their
actual derived categories, naturally in all derived morphisms. -/
def exactDerivedHomologyIso (q : ℤ) :
    F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor D q ≅
      DerivedCategory.homologyFunctor C q ⋙ F :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) _ _ _ _
    (exactDerivedHomologyIsoOnComplexes F q)

/-- The descended isomorphism recovers the canonical complex comparison on
every localization representative. -/
@[simp]
theorem exactDerivedHomologyIso_hom_app_Q_obj
    (q : ℤ) (K : CochainComplex C ℤ) :
    (exactDerivedHomologyIso F q).hom.app (DerivedCategory.Q.obj K) =
      (exactDerivedHomologyIsoOnComplexes F q).hom.app K := by
  simp [exactDerivedHomologyIso, Localization.liftNatIso,
    Localization.liftNatTrans_app, Localization.Lifting.iso]

/-- The isomorphism intertwines every morphism in the derived category. -/
@[reassoc]
theorem exactDerivedHomologyIso_naturality (q : ℤ)
    {K L : DerivedCategory C} (f : K ⟶ L) :
    (DerivedCategory.homologyFunctor D q).map (F.mapDerivedCategory.map f) ≫
        (exactDerivedHomologyIso F q).hom.app L =
      (exactDerivedHomologyIso F q).hom.app K ≫
        F.map ((DerivedCategory.homologyFunctor C q).map f) :=
  (exactDerivedHomologyIso F q).hom.naturality f

end Langlands.Cohomology

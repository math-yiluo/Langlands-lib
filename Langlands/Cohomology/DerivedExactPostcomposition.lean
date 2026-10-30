import Langlands.Cohomology.AcyclicResolution.DerivedComparison
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Exact postcomposition of actual derived complexes

Applying an exact functor to the actual derived complex of an additive functor
agrees naturally with deriving the composite. The comparison is computed with
any injective resolution of the coefficient object.
-/

noncomputable section

namespace Langlands.Cohomology.DerivedPlus

open CategoryTheory CategoryTheory.Limits
open AcyclicResolution

universe wC wD wE vC vD vE uC uD uE

variable {C : Type uC} [Category.{vC} C] [Abelian C]
  [HasDerivedCategory.{wC} C] [EnoughInjectives C]
  {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{wD} D]
  {E : Type uE} [Category.{vE} E] [Abelian E] [HasDerivedCategory.{wE} E]
  (F : C ⥤ D) [F.Additive] (P : D ⥤ E) [P.Additive]
  [PreservesFiniteLimits P] [PreservesFiniteColimits P]

/-- Exact postcomposition on the localized image of an arbitrary
natural-indexed complex. -/
def resolutionPostcompNatIso :
    derivedResolutionFunctor F ⋙ P.mapDerivedCategory ≅
      derivedResolutionFunctor (F ⋙ P) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (ComplexShape.embeddingUpNat.extendFunctor C)
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
          P.mapDerivedCategoryFactors ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ P)) (ComplexShape.up ℤ))
          DerivedCategory.Q)

/-- Compute exact postcomposition of the derived complex with a specified
injective resolution. -/
def derivedPostcompIsoOfResolution {X : C} (I : InjectiveResolution X) :
    P.mapDerivedCategory.obj ((derivedComplex F ⋙ DerivedCategory.Plus.ι).obj X) ≅
      (derivedComplex (F ⋙ P) ⋙ DerivedCategory.Plus.ι).obj X :=
  P.mapDerivedCategory.mapIso (derivedResolutionIso F I) ≪≫
    (resolutionPostcompNatIso F P).app I.cocomplex ≪≫
    (derivedResolutionIso (F ⋙ P) I).symm

set_option backward.isDefEq.respectTransparency false in
/-- The resolution formula commutes with every morphism of injective
resolutions over a coefficient morphism. -/
@[reassoc]
theorem derivedPostcompIsoOfResolution_hom_naturality
    {X Y : C} {f : X ⟶ Y} {I : InjectiveResolution X} {J : InjectiveResolution Y}
    (φ : InjectiveResolution.Hom I J f) :
    P.mapDerivedCategory.map ((derivedComplex F ⋙ DerivedCategory.Plus.ι).map f) ≫
        (derivedPostcompIsoOfResolution F P J).hom =
      (derivedPostcompIsoOfResolution F P I).hom ≫
        (derivedComplex (F ⋙ P) ⋙ DerivedCategory.Plus.ι).map f := by
  have h₁ := derivedResolutionIso_hom_naturality F φ
  have h₂ := (resolutionPostcompNatIso F P).hom.naturality φ.hom
  have h₃ := derivedResolutionIso_hom_naturality (F ⋙ P) φ
  have h₃' :
      (derivedResolutionFunctor (F ⋙ P)).map φ.hom ≫
          (derivedResolutionIso (F ⋙ P) J).inv =
        (derivedResolutionIso (F ⋙ P) I).inv ≫
          (derivedComplex (F ⋙ P) ⋙ DerivedCategory.Plus.ι).map f := by
    rw [← cancel_mono (derivedResolutionIso (F ⋙ P) J).hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [h₃, Iso.inv_hom_id_assoc]
  simp only [derivedPostcompIsoOfResolution, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Iso.app_hom, Category.assoc]
  rw [← P.mapDerivedCategory.map_comp_assoc, h₁, Functor.map_comp, Category.assoc,
    reassoc_of% h₂, h₃']

/-- The comparison is independent of the injective resolution used to
compute it. -/
theorem derivedPostcompIsoOfResolution_hom_eq {X : C}
    (I J : InjectiveResolution X) :
    (derivedPostcompIsoOfResolution F P I).hom =
      (derivedPostcompIsoOfResolution F P J).hom := by
  have h := derivedPostcompIsoOfResolution_hom_naturality F P (descHom (𝟙 X) I J)
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id] at h
  exact h.symm

/-- Deriving an additive functor commutes naturally with exact
postcomposition, in the actual unbounded derived category. -/
def derivedPostcompIso :
    (derivedComplex F ⋙ DerivedCategory.Plus.ι) ⋙ P.mapDerivedCategory ≅
      derivedComplex (F ⋙ P) ⋙ DerivedCategory.Plus.ι :=
  NatIso.ofComponents
    (fun X => derivedPostcompIsoOfResolution F P (injectiveResolution X))
    (fun f => derivedPostcompIsoOfResolution_hom_naturality F P (descHom f _ _))

/-- Every injective resolution computes the component of the natural
comparison isomorphism. -/
theorem derivedPostcompIso_hom_app {X : C} (I : InjectiveResolution X) :
    (derivedPostcompIso F P).hom.app X =
      (derivedPostcompIsoOfResolution F P I).hom :=
  derivedPostcompIsoOfResolution_hom_eq F P _ I

/-- The comparison is exactly the termwise postcomposition comparison after
passing to either injective-resolution model. -/
@[reassoc]
theorem derivedPostcompIso_hom_resolution {X : C} (I : InjectiveResolution X) :
    (derivedPostcompIso F P).hom.app X ≫ (derivedResolutionIso (F ⋙ P) I).hom =
      P.mapDerivedCategory.map (derivedResolutionIso F I).hom ≫
        (resolutionPostcompNatIso F P).hom.app I.cocomplex := by
  rw [derivedPostcompIso_hom_app F P I]
  simp only [derivedPostcompIsoOfResolution, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Iso.app_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end Langlands.Cohomology.DerivedPlus

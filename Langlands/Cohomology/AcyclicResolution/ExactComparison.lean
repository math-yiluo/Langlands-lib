import Langlands.Cohomology.AcyclicResolution.Composition
import Langlands.Cohomology.DerivedComparison
import Langlands.Cohomology.DerivedExactComposition

/-! # Exact comparison through an arbitrary right resolution -/

noncomputable section

universe uC vC uD vD uE vE uE' vE'

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace Langlands.Cohomology.AcyclicResolution

variable {C : Type uC} [Category.{vC} C] [Abelian C]
  {D : Type uD} [Category.{vD} D] [Abelian D]

/-- An exact additive functor maps a right resolution to a right resolution. -/
instance quasiIso_mapResolutionAugmentation
    (T : C ⥤ D) [T.Additive] [T.PreservesHomology]
    {A : C} {K : CochainComplex C ℕ}
    (ε : (CochainComplex.single₀ C).obj A ⟶ K) [QuasiIso ε] :
    QuasiIso (mapResolutionAugmentation T ε) := by
  unfold mapResolutionAugmentation
  infer_instance

section Comparison

open DerivedComparison

variable {E : Type uE} [Category.{vE} E] [Abelian E]
  {E' : Type uE'} [Category.{vE'} E'] [Abelian E']
  (Φ : C ⥤ E) [Φ.Additive] (P : E ⥤ E') [P.Additive] [P.PreservesHomology]
  (T : C ⥤ D) [T.Additive] (Ψ : D ⥤ E') [Ψ.Additive]
  (e : Φ ⋙ P ≅ T ⋙ Ψ)

/-- The specified comparison on the cohomology of an arbitrary complex. -/
def resolutionComplexComparisonIso (K : CochainComplex C ℕ) (n : ℕ) :
    P.obj ((Φ.mapHomologicalComplex _ ⋙ homologyFunctor E _ n).obj K) ≅
      (Ψ.mapHomologicalComplex _ ⋙ homologyFunctor E' _ n).obj
        ((T.mapHomologicalComplex _).obj K) :=
  (mapHomologyIso P ((Φ.mapHomologicalComplex _).obj K) n).symm ≪≫
    (homologyFunctor E' _ n).mapIso (complexIso Φ P T Ψ e K)

/-- The comparison on cohomology is natural in the complex. -/
@[reassoc]
lemma resolutionComplexComparisonIso_hom_naturality
    {K L : CochainComplex C ℕ} (t : K ⟶ L) (n : ℕ) :
    P.map ((Φ.mapHomologicalComplex _ ⋙ homologyFunctor E _ n).map t) ≫
        (resolutionComplexComparisonIso Φ P T Ψ e L n).hom =
      (resolutionComplexComparisonIso Φ P T Ψ e K n).hom ≫
        (Ψ.mapHomologicalComplex _ ⋙ homologyFunctor E' _ n).map
          ((T.mapHomologicalComplex _).map t) := by
  simp only [resolutionComplexComparisonIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Category.assoc, Functor.comp_map]
  rw [mapHomologyIso_inv_naturality_assoc, ← Functor.map_comp,
    complexIso_hom_naturality, Functor.map_comp]

variable [HasInjectiveResolutions C] [HasInjectiveResolutions D]
  [T.PreservesHomology] [T.PreservesInjectiveObjects]
  {A : C} {K : CochainComplex C ℕ}
  (ε : (CochainComplex.single₀ C).obj A ⟶ K) [QuasiIso ε]

/-- The published exact-functor derived comparison is computed by any right resolution. -/
@[reassoc]
theorem resolutionComparison_rightDerivedCompIso (n : ℕ) :
    P.map (resolutionComparison Φ ε n) ≫
        (rightDerivedCompIso Φ P T Ψ e n).hom.app A =
      (resolutionComplexComparisonIso Φ P T Ψ e K n).hom ≫
        resolutionComparison Ψ (mapResolutionAugmentation T ε) n := by
  let I := injectiveResolution A
  let t := lift ε (𝟙 A) I.ι
  have ht : ε ≫ t = I.ι := comp_lift_id ε I
  have hmap : mapResolutionAugmentation T ε ≫ (T.mapHomologicalComplex _).map t =
      (mapInjectiveResolution T I).ι := by
    rw [mapResolutionAugmentation, Category.assoc, ← Functor.map_comp, ht]
  rw [resolutionComparison_eq Φ ε I t ht,
    resolutionComparison_eq Ψ (mapResolutionAugmentation T ε)
      (mapInjectiveResolution T I) ((T.mapHomologicalComplex _).map t) hmap]
  change P.map (comparison Φ I t n) ≫ (compIsoOfResolution Φ P T Ψ e I n).hom = _
  simp only [comparison, compIsoOfResolution, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [← P.map_comp_assoc (I.isoRightDerivedObj Φ n).inv (I.isoRightDerivedObj Φ n).hom,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
  simpa only [resolutionComplexComparisonIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Category.assoc, Functor.comp_map] using
    resolutionComplexComparisonIso_hom_naturality_assoc Φ P T Ψ e t n
      ((mapInjectiveResolution T I).isoRightDerivedObj Ψ n).inv

end Comparison

section Postcomposition

open DerivedComparison

variable {E : Type uE} [Category.{vE} E] [Abelian E]
  {E' : Type uE'} [Category.{vE'} E'] [Abelian E']
  [HasInjectiveResolutions C]
  (Φ : C ⥤ E) [Φ.Additive] (P : E ⥤ E') [P.Additive]
  [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  {H : C ⥤ E'} [H.Additive] (e : Φ ⋙ P ≅ H)
  {A : C} {K : CochainComplex C ℕ}
  (ε : (CochainComplex.single₀ C).obj A ⟶ K) [QuasiIso ε]

/-- Exact postcomposition of the derived comparison is computed by any right resolution. -/
@[reassoc]
theorem resolutionComparison_rightDerivedCompIsoOfResolution (n : ℕ) :
    P.map (resolutionComparison Φ ε n) ≫
        (DerivedPlus.rightDerivedCompIsoOfResolution Φ P e (injectiveResolution A) n).hom =
      (mapHomologyIso P ((Φ.mapHomologicalComplex _).obj K) n).inv ≫
        (homologyFunctor E' _ n).map
          ((Functor.mapHomologicalComplexCompIso e _).hom.app K) ≫
        resolutionComparison H ε n := by
  let I := injectiveResolution A
  let t := lift ε (𝟙 A) I.ι
  have ht : ε ≫ t = I.ι := comp_lift_id ε I
  rw [resolutionComparison_eq Φ ε I t ht, resolutionComparison_eq H ε I t ht]
  simp only [comparison, DerivedPlus.rightDerivedCompIsoOfResolution_hom,
    Functor.map_comp, Functor.comp_map, Category.assoc]
  rw [← P.map_comp_assoc (I.isoRightDerivedObj Φ n).inv (I.isoRightDerivedObj Φ n).hom,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
  change P.map ((homologyFunctor E _ n).map ((Φ.mapHomologicalComplex _).map t)) ≫
      (mapHomologyIso P ((Φ.mapHomologicalComplex _).obj I.cocomplex) n).inv ≫
      (homologyFunctor E' _ n).map
        ((Functor.mapHomologicalComplexCompIso e _).hom.app I.cocomplex) ≫
      (I.isoRightDerivedObj H n).inv = _
  rw [mapHomologyIso_inv_naturality_assoc]
  have hn := (Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℕ)).hom.naturality t
  simp only [Functor.comp_map] at hn
  rw [← (homologyFunctor E' (ComplexShape.up ℕ) n).map_comp_assoc, hn,
    Functor.map_comp_assoc]

/-- The inverse exact-postcomposition comparison is computed by the inverse
termwise comparison on any right resolution. -/
@[reassoc]
theorem resolutionComparison_inv_rightDerivedCompIsoOfResolution (n : ℕ) :
    resolutionComparison H ε n ≫
        (DerivedPlus.rightDerivedCompIsoOfResolution Φ P e (injectiveResolution A) n).inv =
      (homologyFunctor E' _ n).map
          ((Functor.mapHomologicalComplexCompIso e _).inv.app K) ≫
        (mapHomologyIso P ((Φ.mapHomologicalComplex _).obj K) n).hom ≫
        P.map (resolutionComparison Φ ε n) := by
  apply (cancel_mono
    (DerivedPlus.rightDerivedCompIsoOfResolution Φ P e (injectiveResolution A) n).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [resolutionComparison_rightDerivedCompIsoOfResolution]
  rw [Iso.hom_inv_id_assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]

end Postcomposition

end Langlands.Cohomology.AcyclicResolution

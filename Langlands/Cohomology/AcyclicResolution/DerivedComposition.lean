import Langlands.Cohomology.AcyclicResolution.DerivedCompositeComparison
import Langlands.Cohomology.AcyclicResolution.Composition
import Langlands.Cohomology.DerivedExactComposition

/-! # Derived composite comparisons through arbitrary right resolutions -/

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace Langlands.Cohomology.AcyclicResolution

universe wC wD wE vC vD vE uC uD uE

section Composite

variable {C : Type uC} [Category.{vC} C] [Abelian C]
  [HasDerivedCategory.{wC} C] [EnoughInjectives C]
  {D : Type uD} [Category.{vD} D] [Abelian D]
  [HasDerivedCategory.{wD} D] [EnoughInjectives D]
  {E : Type uE} [Category.{vE} E] [Abelian E] [HasDerivedCategory.{wE} E]
  {F : C ⥤ D} [F.Additive] [PreservesFiniteLimits F]
  (G : D ⥤ E) [G.Additive] {H : C ⥤ E} [H.Additive]
  (e : F ⋙ G ≅ H) {A : C} {K : CochainComplex C ℕ}
  (ε : (CochainComplex.single₀ C).obj A ⟶ K) [QuasiIso ε]
  [QuasiIso (mapResolutionAugmentation F ε)]

set_option backward.isDefEq.respectTransparency false in
/-- The actual composite-functor comparison can be computed with any right
resolution whose mapped augmentation is again a quasi-isomorphism. -/
@[reassoc]
theorem derivedResolutionComparison_compComparison
    (hA : ∀ q : ℕ, IsZero ((F.rightDerived (q + 1)).obj A)) :
    derivedResolutionComparison H ε ≫ derivedCompComparison G e A hA =
      (derivedCompResolutionIso G e K).hom ≫
        derivedResolutionComparison G (mapResolutionAugmentation F ε) := by
  let I := injectiveResolution A
  let t := lift ε (𝟙 A) I.ι
  have ht : ε ≫ t = I.ι := comp_lift_id ε I
  have := quasiIso_mapAugmentation F I hA
  have hmap : mapResolutionAugmentation F ε ≫ (F.mapHomologicalComplex _).map t =
      mapAugmentation F I := by
    rw [mapResolutionAugmentation, Category.assoc, ← Functor.map_comp, ht]
    exact mapResolutionAugmentation_injectiveResolution F I
  have hc := derivedResolutionComparison_naturality G (mapResolutionAugmentation F ε)
    (mapAugmentation F I) (𝟙 (F.obj A)) ((F.mapHomologicalComplex _).map t)
    (by simpa only [CategoryTheory.Functor.map_id, Category.id_comp] using hmap)
  simp only [CategoryTheory.Functor.map_id, Category.comp_id] at hc
  rw [derivedResolutionComparison_eq H ε I t ht]
  simp only [derivedComparison, derivedCompComparison, derivedCompComparisonWithResolution,
    Category.assoc]
  rw [Iso.inv_hom_id_assoc, derivedCompResolutionIso_hom_naturality_assoc, hc]

end Composite

section Postcomposition

open DerivedPlus

variable {C : Type uC} [Category.{vC} C] [Abelian C]
  [HasDerivedCategory.{wC} C] [EnoughInjectives C]
  {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{wD} D]
  {E : Type uE} [Category.{vE} E] [Abelian E] [HasDerivedCategory.{wE} E]
  (G : C ⥤ D) [G.Additive] (P : D ⥤ E) [P.Additive]
  [PreservesFiniteLimits P] [PreservesFiniteColimits P]
  {H : C ⥤ E} [H.Additive] (e : G ⋙ P ≅ H)

/-- Exact postcomposition and a specified functor isomorphism on the
localized image of a natural-indexed complex. -/
def derivedResolutionPostcompIso (K : CochainComplex C ℕ) :
    P.mapDerivedCategory.obj ((derivedResolutionFunctor G).obj K) ≅
      (derivedResolutionFunctor H).obj K :=
  (resolutionPostcompNatIso G P).app K ≪≫ (resolutionCongrNatIso e).app K

variable {A : C} {K : CochainComplex C ℕ}
  (ε : (CochainComplex.single₀ C).obj A ⟶ K) [QuasiIso ε]

set_option backward.isDefEq.respectTransparency false in
/-- Exact postcomposition of the actual derived comparison is computed by
the specified termwise isomorphism on any right resolution. -/
@[reassoc]
theorem derivedResolutionComparison_derivedCompIso :
    P.mapDerivedCategory.map (derivedResolutionComparison G ε) ≫
        (derivedCompIso G P e).hom.app A =
      (derivedResolutionPostcompIso G P e K).hom ≫
        derivedResolutionComparison H ε := by
  let I := injectiveResolution A
  let t := lift ε (𝟙 A) I.ι
  have ht : ε ≫ t = I.ι := comp_lift_id ε I
  rw [derivedResolutionComparison_eq G ε I t ht,
    derivedResolutionComparison_eq H ε I t ht]
  apply (cancel_mono (derivedResolutionIso H I).hom).1
  simp only [derivedComparison, Category.assoc]
  rw [derivedCompIso_hom_resolution]
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← P.mapDerivedCategory.map_comp_assoc (derivedResolutionIso G I).inv
    (derivedResolutionIso G I).hom, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp]
  simpa only [derivedResolutionPostcompIso, Iso.trans_hom, Iso.app_hom,
    NatTrans.comp_app, Functor.comp_map, Category.assoc] using
    (resolutionPostcompNatIso G P ≪≫ resolutionCongrNatIso e).hom.naturality t

/-- Inverse form of the exact-postcomposition identity on a right resolution. -/
@[reassoc]
theorem derivedResolutionComparison_inv_derivedCompIso :
    derivedResolutionComparison H ε ≫ (derivedCompIso G P e).inv.app A =
      (derivedResolutionPostcompIso G P e K).inv ≫
        P.mapDerivedCategory.map (derivedResolutionComparison G ε) := by
  apply (cancel_mono ((derivedCompIso G P e).hom.app A)).1
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [derivedResolutionComparison_derivedCompIso, Iso.inv_hom_id_assoc]

end Postcomposition

end Langlands.Cohomology.AcyclicResolution

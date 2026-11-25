/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Strict.StrictScalarKoszulInstances
import all WeilConjectures.CategoryTheory.Koszul.KoszulModuleBasisEvaluation

/-! # KoszulTensorEvaluationComponents for strict Koszul comparison

Source: Stacks Project, Tags 0A0E and 0913.
(blueprint: lem-f5-koszul-tensor-evaluation-components).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.FlatScalarKoszul

variable {S : Type u} [SmallCategory S] {J : GrothendieckTopology S}
variable {R B : Sheaf J CommRingCat.{u}}

open MonoidalCategory
open scoped CategoryTheory.Prod

attribute [local irreducible] homComplexFunctor
  SheafOfModules.tensorObjIsoSheafification PresheafOfModules.sheafificationAdjunction
  Localization.Monoidal.tensorBifunctor

attribute [local instance] gradedTensorCache gradedGoodTensorLeftCache
  gradedGoodTensorRightCache gradedFourCache tensorPreservesEmptyLeftCache
  tensorPreservesEmptyRightCache cachedModuleMonoidal cachedModuleSymmetric
  cachedModulePreadditive cachedModuleClosed cachedComplexMonoidal
  cachedComplexBraided cachedComplexClosed

/-- Move a unit basis vector through braiding and contract the resulting tensor.
Source: Stacks Project, Tags 0A0E and 0913 (finite Koszul tensor calculation).
(blueprint: lem-f5-koszul-tensor-evaluation-components). -/
theorem basisContraction {D : Type*} [Category D] [MonoidalCategory D]
    [BraidedCategory D] {P X Y : D} (b : 𝟙_ D ⟶ P) (g : P ⊗ Y ⟶ 𝟙_ D) :
    (λ_ (X ⊗ Y)).inv ≫ b ▷ (X ⊗ Y) ≫ P ◁ (β_ X Y).hom ≫
        (α_ P Y X).inv ≫ g ▷ X ≫ (λ_ X).hom =
      X ◁ ((λ_ Y).inv ≫ b ▷ Y ≫ g) ≫ (ρ_ X).hom := by
  rw [← whisker_exchange_assoc, ← leftUnitor_inv_naturality_assoc,
    associator_inv_naturality_left_assoc, leftUnitor_tensor_inv]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← comp_whiskerRight_assoc, ← comp_whiskerRight_assoc,
    ← BraidedCategory.braiding_naturality_right_assoc,
    braiding_tensorUnit_right]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

private def evaluationUncurry (O : Sheaf J CommRingCat.{u})
    (P N : ringedSiteComplex O) :
    let : IsGrothendieckAbelian.{u} (Modules O) := SheafOfModules.isGrothendieckAbelian _
    let := cachedModuleMonoidal O
    let := cachedModuleSymmetric O
    let := cachedModulePreadditive O
    let := cachedModuleClosed O
    let := cachedComplexClosed O
    P ⊗ (N ⊗ homComplex (R := O) P (ringedSiteRingComplex O)) ⟶ N := by
  let : IsGrothendieckAbelian.{u} (Modules O) := SheafOfModules.isGrothendieckAbelian _
  let := cachedModuleMonoidal O
  let := cachedModuleSymmetric O
  let := cachedModulePreadditive O
  let := cachedModuleClosed O
  let := cachedComplexClosed O
  dsimp only
  exact evaluationUncurryCore P N

private theorem evaluation_eq_curry (O : Sheaf J CommRingCat.{u})
    (P N : ringedSiteComplex O) :
    let : IsGrothendieckAbelian.{u} (Modules O) := SheafOfModules.isGrothendieckAbelian _
    let := cachedModuleMonoidal O
    let := cachedModuleSymmetric O
    let := cachedModulePreadditive O
    let := cachedModuleClosed O
    let := cachedComplexClosed O
    ringedComplexTensorEvaluation O P N = MonoidalClosed.curry (evaluationUncurry O P N) := by
  let : IsGrothendieckAbelian.{u} (Modules O) := SheafOfModules.isGrothendieckAbelian _
  let := cachedModuleMonoidal O
  let := cachedModuleSymmetric O
  let := cachedModulePreadditive O
  let := cachedModuleClosed O
  let := cachedComplexClosed O
  dsimp only
  unfold ringedComplexTensorEvaluation evaluationUncurry
  exact evaluationCurryCore P N

private theorem tripleEvaluation_component
    {E : Type*} [Category E] [Abelian E] [MonoidalCategory E]
    [SymmetricCategory E] [MonoidalPreadditive E] [MonoidalClosed E]
    [HasCoproducts.{0} E]
    [∀ (X₁ X₂ : GradedObject ℤ E), X₁.HasTensor X₂]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ E), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ E), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    (P N D : CochainComplex E ℤ) (g : P ⊗ D ⟶ 𝟙_ (CochainComplex E ℤ))
    (d p q t k : ℤ) (ht : d + q = t) (h : d + p + q = k) :
    HomologicalComplex.mapBifunctor₂₃.ι (curriedTensor E) (curriedTensor E) P N D
        (.up ℤ) (.up ℤ) (.up ℤ) d p q k h ≫
        (P ◁ (β_ N D).hom ≫ (α_ P D N).inv ≫ g ▷ N ≫ (λ_ N).hom).f k =
      (p * q).negOnePow •
        (P.X d ◁ (β_ (N.X p) (D.X q)).hom ≫
          (α_ (P.X d) (D.X q) (N.X p)).inv ≫
          (HomologicalComplex.ιTensorObj P D d q t ht ≫ g.f t) ▷ N.X p ≫
          HomologicalComplex.ιTensorObj (𝟙_ (CochainComplex E ℤ)) N t p k (by omega) ≫
          (λ_ N).hom.f k) := by
  simp only [HomologicalComplex.comp_f]
  erw [CochainComplex.Monoidal.ι₂₃_eq P N D d p q (p + q) k rfl (by omega),
    Category.assoc, CochainComplex.ιTensorObj_whiskerLeft_f_assoc P (β_ N D).hom d (p + q) k
      (by omega),
    ← whiskerLeft_comp_assoc,
    CochainComplex.Monoidal.ι_braiding_hom (K := N) (L := D) p q (p + q) rfl]
  simp only [Units.smul_def, whiskerLeft_zsmul, Preadditive.zsmul_comp]
  erw [whiskerLeft_comp, Category.assoc,
    ← reassoc_of% (CochainComplex.Monoidal.ι₂₃_eq P D N d q p (p + q) k
      (add_comm q p) (by omega)),
    CochainComplex.Monoidal.ι₂₃_associator_inv_assoc P D N d q p k (by omega),
    CochainComplex.Monoidal.ι₁₂_eq P D N d q p t k ht (by omega)]
  simp only [Category.assoc]
  erw [CochainComplex.Monoidal.ι_whiskerRight_assoc (L := N) g t p k (by omega),
    ← comp_whiskerRight_assoc]

private theorem signedTripleEvaluation_component
    {E : Type*} [Category E] [Abelian E] [MonoidalCategory E]
    [SymmetricCategory E] [MonoidalPreadditive E] [MonoidalClosed E]
    [HasCoproducts.{0} E]
    [∀ (X₁ X₂ : GradedObject ℤ E), X₁.HasTensor X₂]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ E), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ E), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    (P N D : CochainComplex E ℤ) (g : P ⊗ D ⟶ 𝟙_ (CochainComplex E ℤ))
    (d p q t k : ℤ) (ht : d + q = t) (h : d + p + q = k)
    (s : ℤˣ) (e : P.X d ⊗ D.X q ⟶ (𝟙_ (CochainComplex E ℤ)).X t)
    (hg : HomologicalComplex.ιTensorObj P D d q t ht ≫ g.f t = s • e) :
    HomologicalComplex.mapBifunctor₂₃.ι (curriedTensor E) (curriedTensor E) P N D
        (.up ℤ) (.up ℤ) (.up ℤ) d p q k h ≫
        (P ◁ (β_ N D).hom ≫ (α_ P D N).inv ≫ g ▷ N ≫ (λ_ N).hom).f k =
      ((p * q).negOnePow * s) •
        (P.X d ◁ (β_ (N.X p) (D.X q)).hom ≫
          (α_ (P.X d) (D.X q) (N.X p)).inv ≫ e ▷ N.X p ≫
          HomologicalComplex.ιTensorObj (𝟙_ (CochainComplex E ℤ)) N t p k (by omega) ≫
          (λ_ N).hom.f k) := by
  rw [tripleEvaluation_component P N D g d p q t k ht h, hg]
  simp only [Units.smul_def, zsmul_whiskerRight, Preadditive.comp_zsmul,
    Preadditive.zsmul_comp, smul_smul, Units.val_mul]

-- Normalize the recursive total-tensor basis and its component inclusions.
/-- Homogeneous components of uncurried tensor-Hom evaluation.
Source: Stacks Project, Tags 0A0E and 0913 (finite Koszul tensor calculation).
Proof step 1: Define the uncurried evaluation as the braiding, inverse associator, evaluation and
left unitor. Curry naturality identifies its curry with canonical tensor-Hom evaluation.
Proof step 2: Rewrite the threefold total inclusion through the braiding and associator using
their named inclusion identities. The braiding contributes (-1)^(pq); the evaluation component
identity contributes (-1)^(dq). Combine these signs using bilinearity.
Proof step 3: The basis contraction identity follows from braiding naturality and its unit
formulas: moving a unit basis vector past a tensor then evaluating is exactly right whiskering by
evaluation against that basis. This identifies the module contraction used in the component
formula.
(blueprint: lem-f5-koszul-tensor-evaluation-components). -/
private theorem evaluationUncurry_component (O : Sheaf J CommRingCat.{u})
    (P N : ringedSiteComplex O) (d p q t k : ℤ) (ht : d + q = t) (h : d + p + q = k) :
    let : IsGrothendieckAbelian.{u} (Modules O) := SheafOfModules.isGrothendieckAbelian _
    let := cachedModuleMonoidal O
    let := cachedModuleSymmetric O
    let := cachedModulePreadditive O
    let := cachedModuleClosed O
    let := cachedComplexClosed O
    HomologicalComplex.mapBifunctor₂₃.ι (tensor O) (tensor O) P N
        (homComplex (R := O) P (ringedSiteRingComplex O))
        (.up ℤ) (.up ℤ) (.up ℤ) d p q k h ≫ (evaluationUncurry O P N).f k =
      (p * q + d * q).negOnePow •
        (P.X d ◁ (β_ (N.X p)
            ((homComplex (R := O) P (ringedSiteRingComplex O)).X q)).hom ≫
          (α_ (P.X d) _ (N.X p)).inv ≫
          MonoidalClosed.uncurry
            (homComplexπ P (ringedSiteRingComplex O) q d t ht) ▷ N.X p ≫
          HomologicalComplex.ιTensorObj (ringedSiteRingComplex O) N
            t p k (by omega) ≫ (λ_ N).hom.f k) := by
  let : IsGrothendieckAbelian.{u} (Modules O) := SheafOfModules.isGrothendieckAbelian _
  let := cachedModuleMonoidal O
  let := cachedModuleSymmetric O
  let := cachedModulePreadditive O
  let := cachedModuleClosed O
  let := cachedComplexClosed O
  dsimp only
  let D := homComplex (R := O) P (ringedSiteRingComplex O)
  change HomologicalComplex.mapBifunctor₂₃.ι (tensor O) (tensor O) P N D
      (.up ℤ) (.up ℤ) (.up ℤ) d p q k h ≫
      (P ◁ (β_ N D).hom ≫ (α_ P D N).inv ≫
        (ihom.ev P).app (𝟙_ (ringedSiteComplex O)) ▷ N ≫ (λ_ N).hom).f k = _
  simpa only [Int.negOnePow_add] using!
    signedTripleEvaluation_component P N D ((ihom.ev P).app
      (𝟙_ (ringedSiteComplex O))) d p q t k ht h (d * q).negOnePow
      (MonoidalClosed.uncurry (homComplexπ P (ringedSiteRingComplex O) q d t ht))
      (complexEvaluation_component O P (ringedSiteRingComplex O) d q t ht)

end CategoryTheory.FlatScalarKoszul

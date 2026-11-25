/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ConstantKoszulTensorIdentifications

/-! # The normalized Koszul augmentation at one finite level
Source: Stacks 099M and 06YN (auxiliary; not a blueprint node).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace CategoryTheory.ConstantCompletion.KoszulTensorComparison
open TensorComparison
variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
variable (A : Type u) [CommRing A] (I : Ideal A)

attribute [local instance] TensorComparison.tensorTower_additive

attribute [local instance] flatConstantCochainMonoidal flatConstantCochainMonoidalStruct
  SheafOfModules.monoidalCategory Functor.preservesZeroMorphisms_of_additive

private theorem augmentationModelUnitAt
    (b : Bool) (r : ℕ) (a : Fin r → A)
    (α : ringedKoszulTensorTowerFunctor (coefficients J A I b) r
        (fun i ↦ algebraSection (baseMap J A I b) (a i)) ⟶
      (reductionTower J A I b).mapHomologicalComplex (.up ℤ))
    (hα : KoszulQuotientAugmentationLaws J A I b r a α)
    (e : reductionTower J A I b ≅
      tensorTower J (coefficients J A I b)
        ((reductionTower J A I b).obj (𝟙_ (Mod (coefficients J A I b)))))
    (he : ∀ (M : Mod (coefficients J A I b)) (n : ℕᵒᵖ),
      ((reductionUnit J A I b).app M).app n ≫ (e.hom.app M).app n =
        (ρ_ M).inv ≫ M ◁
          ((reductionUnit J A I b).app (𝟙_ (Mod (coefficients J A I b)))).app n)
    (M : Cx (coefficients J A I b)) (n : ℕ) (p : ℤ) :
    let O := coefficients J A I b
    let s := fun i ↦ algebraSection (baseMap J A I b) (a i)
    let K := (ringedKoszulDualTower O r s).obj (op n)
    (ρ_ (M.X p)).inv ≫ M.X p ◁
      ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).inv ≫
        (ringedKoszulDualUnit O r s n).f 0) ≫
      HomologicalComplex.ιTensorObj M K p 0 p (add_zero p) ≫
        ((koszulEvaluationIso J O r s M (op n)).inv ≫
          (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
            (α.app M)).app (op n) ≫
          (reductionModelIso J A I b e M).hom.app (op n)).f p =
      (ρ_ (M.X p)).inv ≫ M.X p ◁
        ((reductionUnit J A I b).app (𝟙_ (Mod O))).app (op n) := by
  dsimp only
  let O := coefficients J A I b
  let s := fun i ↦ algebraSection (baseMap J A I b) (a i)
  have h := congrArg (fun f ↦ f ≫ (e.hom.app (M.X p)).app (op n))
    (augmentationUnitAt J A I b r a α hα M n p)
  rw [he] at h
  rw [koszulTensorUnit_f J O r s M n p] at h
  simp only [HomologicalComplex.comp_f, koszulEvaluationIso_inv_f,
    reductionModelIso_hom_f]
  erw [Category.id_comp]
  exact h

/-- The two normalized augmentation maps satisfy the native tensor square at a finite level.
Source: Stacks 099M and 06YN (auxiliary; not a blueprint node).
Proof: project the ordinary-limit normalization to this level and transport it through
its ordinary tensor model. The negative Koszul degree-zero basis makes its unit
invertible. On every nonzero Koszul summand the transported map vanishes by the
augmentation law. Apply the proved normalization theorem to these three equations.
This is an equality of chain maps at one level, before tower assembly or mapping cones. -/
theorem normalizedAugmentationTensorLevel
    (b : Bool) (r : ℕ) (a : Fin r → A)
    (α : ringedKoszulTensorTowerFunctor (coefficients J A I b) r
        (fun i ↦ algebraSection (baseMap J A I b) (a i)) ⟶
      (reductionTower J A I b).mapHomologicalComplex (.up ℤ))
    (hα : KoszulQuotientAugmentationLaws J A I b r a α)
    (e : reductionTower J A I b ≅
      tensorTower J (coefficients J A I b)
        ((reductionTower J A I b).obj (𝟙_ (Mod (coefficients J A I b)))))
    (he : ∀ (M : Mod (coefficients J A I b)) (n : ℕᵒᵖ),
      ((reductionUnit J A I b).app M).app n ≫ (e.hom.app M).app n =
        (ρ_ M).inv ≫ M ◁
          ((reductionUnit J A I b).app (𝟙_ (Mod (coefficients J A I b)))).app n)
    (P : Cx (coefficients J A I b)) (n : ℕ) :
    let O := coefficients J A I b
    let s := fun i ↦ algebraSection (baseMap J A I b) (a i)
    let K := (ringedKoszulDualTower O r s).obj (op n)
    let Q := ((reductionTower J A I b).obj (𝟙_ (Mod O))).obj (op n)
    let U := ringedSiteRingComplex O
    let bP := (koszulEvaluationIso J O r s P (op n)).inv ≫
      (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map (α.app P)).app (op n) ≫
      (reductionModelIso J A I b e P).hom.app (op n)
    let bU := (koszulEvaluationIso J O r s U (op n)).inv ≫
      (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map (α.app U)).app (op n) ≫
      (reductionModelIso J A I b e U).hom.app (op n)
    P ◁ bU ≫ (quotientTensorIso J O Q P).hom = P ◁ (λ_ K).hom ≫ bP := by
  dsimp only
  let O := coefficients J A I b
  let s := fun i ↦ algebraSection (baseMap J A I b) (a i)
  let K := (ringedKoszulDualTower O r s).obj (op n)
  let Q := ((reductionTower J A I b).obj (𝟙_ (Mod O))).obj (op n)
  let U := ringedSiteRingComplex O
  let bP := (koszulEvaluationIso J O r s P (op n)).inv ≫
    (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map (α.app P)).app (op n) ≫
    (reductionModelIso J A I b e P).hom.app (op n)
  let bU := (koszulEvaluationIso J O r s U (op n)).inv ≫
    (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map (α.app U)).app (op n) ≫
    (reductionModelIso J A I b e U).hom.app (op n)
  have hi := koszulUnitZero_isIso J O r s n
  exact normalizedTensorSquare J O K P Q
    ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 _).inv ≫
      (ringedKoszulDualUnit O r s n).f 0)
    (((reductionUnit J A I b).app (𝟙_ (Mod O))).app (op n)) bP bU
    (augmentationModelUnitAt J A I b r a α hα e he P n)
    (augmentationModelUnitAt J A I b r a α hα e he U n) (by
      intro p q hq
      have h := congrArg
        (fun f ↦ f ≫ (e.hom.app (P.X (p + q))).app (op n))
        (hα.2 P n p q hq)
      simp only [bP, HomologicalComplex.comp_f, koszulEvaluationIso_inv_f,
        reductionModelIso_hom_f]
      erw [Category.id_comp]
      exact h.trans (zero_comp))

end CategoryTheory.ConstantCompletion.KoszulTensorComparison

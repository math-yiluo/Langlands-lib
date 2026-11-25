/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ConstantKoszulTensorIdentifications
import WeilConjectures.AlgebraicGeometry.ConstantKoszulTensorLevel

/-! # The normalized Koszul augmentation tensor square
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

/-- Normalized augmentations give a commuting tensor square before taking cones.
Source: Stacks 099M and 06YN (auxiliary; not a blueprint node).
Proof: project the ordinary-limit unit equation to each finite level. Transport
it through the ordinary reduction tensor model. The degree-zero Koszul unit is
invertible by negative Koszul duality and its empty-subset basis. Apply the
normalization theorem to this projected unit equation and to the nonzero-degree
vanishing law. Cancel the source and target comparison isomorphisms at each
level, and use natural-transformation extensionality to assemble the square. -/
theorem augmentationTensorSquare
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
    (P : Cx (coefficients J A I b)) :
    let O := coefficients J A I b
    let s := fun i ↦ algebraSection (baseMap J A I b) (a i)
    let U := ringedSiteRingComplex O
    let β := HomologicalComplex.complexOfFunctorsToFunctorToComplex.map (α.app U)
    let γ := HomologicalComplex.complexOfFunctorsToFunctorToComplex.map (α.app P)
    let E := Functor.isoWhiskerRight (reductionModelIso J A I b e U) (tensorLeft P) ≪≫
      tensorTowerComparison J O ((reductionTower J A I b).obj (𝟙_ (Mod O))) P ≪≫
      (reductionModelIso J A I b e P).symm
    Functor.whiskerRight β (tensorLeft P) ≫ E.hom =
      (koszulSourceTensorIso J O r s P).hom ≫ γ := by
  dsimp only
  apply NatTrans.ext
  funext n
  obtain ⟨n⟩ := n
  let O := coefficients J A I b
  let s := fun i ↦ algebraSection (baseMap J A I b) (a i)
  let K := (ringedKoszulDualTower O r s).obj (op n)
  let Q := ((reductionTower J A I b).obj (𝟙_ (Mod O))).obj (op n)
  let U := ringedSiteRingComplex O
  have hs := normalizedAugmentationTensorLevel J A I b r a α hα e he P n
  apply (cancel_mono ((reductionModelIso J A I b e P).hom.app (op n))).1
  apply (cancel_epi ((tensorLeft P).map
    (koszulEvaluationIso J O r s U (op n)).inv)).1
  dsimp only [O, s, U, K, Q] at hs
  simp only [O, s, U, koszulSourceTensorIso_hom_app,
    tensorTowerComparison, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    NatTrans.comp_app, NatIso.ofComponents_hom_app, Functor.whiskerRight_app,
    Category.assoc,
    ← Functor.map_comp_assoc, Iso.inv_hom_id_app, Category.comp_id]
  erw [Iso.inv_hom_id_assoc]
  exact hs

end CategoryTheory.ConstantCompletion.KoszulTensorComparison

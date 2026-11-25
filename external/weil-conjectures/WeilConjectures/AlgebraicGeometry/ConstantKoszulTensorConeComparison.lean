/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ConstantKoszulQuotientAugmentation
public import WeilConjectures.CategoryTheory.FlatConstantTensorProZeroCones
import WeilConjectures.AlgebraicGeometry.ConstantKoszulTensorSquare
import WeilConjectures.AlgebraicGeometry.TensorConeTowerIso

/-! # Tensor of the normalized coefficient augmentation cone

Source: Stacks Project, Tags 099M, 093M and 0A0E.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace CategoryTheory.ConstantCompletion
variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
variable (A : Type u) [CommRing A] (I : Ideal A)

attribute [local instance] flatConstantCochainMonoidal flatConstantCochainMonoidalStruct

/-- Tensoring the coefficient cone gives the actual cone at an arbitrary complex.
This is a strict tower isomorphism, with no Noetherianity, flatness, localization,
or inverse-limit assertion.

Source: Stacks Project, Tags 099M and 06YP, the signed tensor-cone calculation.
(auxiliary; not a blueprint node).

Proof: at the cochain unit U, identify U tensor the dual Koszul complex with the
dual complex by the left unitor. Scalar tensor cancellation identifies the
reduction of U with the finite quotient in degree zero. For arbitrary P, the
associator and unitors identify P tensor the source at U with the source at P;
the single-degree-zero tensor comparison and scalar tensor cancellation give
the corresponding target isomorphism. On nonzero Koszul-degree summands both
augmentation composites are zero by the vanishing law. In degree zero, the
Koszul unit is invertible, and the ordinary-limit unit equation, composed with
each level projection, identifies both composites with the actual reduction
unit. The total-tensor coproduct inclusions jointly detect the resulting square.
These isomorphisms commute with the transitions by naturality of the unitors,
associator and quotient maps. Apply the signed tensor-cone isomorphism and the
cone map of this square at each level. Its sign on the shifted-source summand
in P-degree p is (-1)^p; the same sign appears on both sides of each transition.
The level isomorphisms therefore assemble into the strict tower isomorphism.
This argument includes the empty generator list, zero ring and empty site. -/
theorem constantKoszulTensorConeComparison
    (b : Bool) (r : ℕ) (a : Fin r → A)
    (α : ringedKoszulTensorTowerFunctor (coefficients J A I b) r
        (fun i ↦ algebraSection (baseMap J A I b) (a i)) ⟶
      (reductionTower J A I b).mapHomologicalComplex (.up ℤ))
    (hα : KoszulQuotientAugmentationLaws J A I b r a α)
    (P : Cx (coefficients J A I b)) :
    Nonempty
      ((CochainComplex.mappingCone
          (α.app (ringedSiteRingComplex (coefficients J A I b)))).asFunctor ⋙
        tensorLeft P ≅ (CochainComplex.mappingCone (α.app P)).asFunctor) := by
  let := SheafOfModules.monoidalCategory (coefficients J A I b)
  let O := coefficients J A I b
  let s := fun i ↦ algebraSection (baseMap J A I b) (a i)
  let U := ringedSiteRingComplex O
  let β := HomologicalComplex.complexOfFunctorsToFunctorToComplex.map (α.app U)
  let γ := HomologicalComplex.complexOfFunctorsToFunctorToComplex.map (α.app P)
  obtain ⟨e, he⟩ := constantReductionTensorModel J A I b
  let E := Functor.isoWhiskerRight
    (KoszulTensorComparison.reductionModelIso J A I b e U) (tensorLeft P) ≪≫
    TensorComparison.tensorTowerComparison J O ((reductionTower J A I b).obj (𝟙_ (Mod O))) P ≪≫
    (KoszulTensorComparison.reductionModelIso J A I b e P).symm
  have h := KoszulTensorComparison.augmentationTensorSquare J A I b r a α hα e he P
  exact tensorConeTowerIso (curriedTensor (Mod O)) P (α.app U) (α.app P)
    (KoszulTensorComparison.koszulSourceTensorIso J O r s P) E h

end CategoryTheory.ConstantCompletion

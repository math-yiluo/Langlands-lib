/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedForgetTwoInjective.RingedForgetTwoInjectiveHom
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement

public import WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedForgetTensorTranspositionData
import WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedForgetNormalizedUncurry

/-! # Normalized tensor and transposition under ringed forgetting

Source: the internal-Hom/evaluation/transposition paragraph of
blueprint/sec-six-functors/sk-thm-sf-package/cor-coef-verdier-weil-equivariance.proof.md;
Stacks Project, Tags 015F, 06YS, 06YU, 0G7D, 0A90, 0A96, 070I, 08J9 and 0FPT
(blueprint: lem-sf-ringed-forget-tensor-transposition).

The auxiliary data below specify the comparisons on actual total-tensor summands.
The double-dual arrow is the transpose of symmetric evaluation, with no invertibility claim.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe b vb a va c v r d vd s wb wa

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite WeilConjectures

namespace CategoryTheory.RingedForgetTensorTransposition

section FormalLaws

variable {B : Type b} [Category.{vb} B] {A : Type a} [Category.{va} A]
  {H : Bᵒᵖ × B ⥤ B} (S : CoefficientClosedStructure H)

private theorem uncurry_eq (T P Q : B) (g : T ⟶ H.obj (op P, Q)) :
    (S.transpose T P Q).symm g =
      S.tensor.map (X := (T, P)) (Y := (H.obj (op P, Q), P))
        (g, 𝟙 P) ≫ S.evaluation P Q := by
  let := S.monoidal
  simp [CoefficientClosedStructure.transpose, CoefficientClosedStructure.evaluation,
    CoefficientClosedStructure.tensor, Adjunction.homEquiv, MonoidalCategory.tensor]

private theorem uncurry_left (T T' P Q : B) (f : T' ⟶ T)
    (g : T ⟶ H.obj (op P, Q)) :
    (S.transpose T' P Q).symm (f ≫ g) =
      S.tensor.map (X := (T', P)) (Y := (T, P)) (f, 𝟙 P) ≫
        (S.transpose T P Q).symm g := by
  let := S.monoidal
  rw [uncurry_eq, uncurry_eq]
  change ((f ≫ g) ⊗ₘ 𝟙 P) ≫ _ = (f ⊗ₘ 𝟙 P) ≫ ((g ⊗ₘ 𝟙 P) ≫ _)
  simp only [tensorHom_comp_tensorHom_assoc, Category.id_comp]

private theorem uncurry_hom (T P P' Q : B) (f : P' ⟶ P)
    (g : T ⟶ H.obj (op P, Q)) :
    (S.transpose T P' Q).symm
        (g ≫ H.map (X := (op P, Q)) (Y := (op P', Q)) (f.op, 𝟙 Q)) =
      S.tensor.map (X := (T, P')) (Y := (T, P)) (𝟙 T, f) ≫
        (S.transpose T P Q).symm g := by
  let := S.monoidal
  have he :
      (H.map (X := (op P, Q)) (Y := (op P', Q)) (f.op, 𝟙 Q) ⊗ₘ 𝟙 P') ≫
          S.evaluation P' Q =
        (𝟙 (H.obj (op P, Q)) ⊗ₘ f) ≫ S.evaluation P Q := by
    simpa [CoefficientClosedStructure.evaluation] using S.evaluation_naturality P P' Q f
  simp only [uncurry_eq]
  change ((g ≫ _) ⊗ₘ 𝟙 P') ≫ _ = (𝟙 T ⊗ₘ f) ≫ ((g ⊗ₘ 𝟙 P) ≫ _)
  calc
    _ = (g ⊗ₘ 𝟙 P') ≫
        ((H.map (X := (op P, Q)) (Y := (op P', Q)) (f.op, 𝟙 Q) ⊗ₘ 𝟙 P') ≫
          S.evaluation P' Q) := by simp
    _ = (g ⊗ₘ 𝟙 P') ≫ ((𝟙 (H.obj (op P, Q)) ⊗ₘ f) ≫ S.evaluation P Q) := by
      rw [he]
    _ = _ := by
      simp only [tensorHom_comp_tensorHom_assoc, Category.comp_id, Category.id_comp]

private theorem delta_uncurry (β : @SymmetricCategory B _ S.monoidal) (W K : B) :
    (S.transpose K (H.obj (op K, W)) W).symm (delta S β W K) =
      (β.toBraidedCategory.braiding K (H.obj (op K, W))).hom ≫ S.evaluation K W :=
  (S.transpose _ _ _).symm_apply_apply _

private theorem delta_natural (β : @SymmetricCategory B _ S.monoidal)
    (W K K' : B) (f : K ⟶ K') :
    delta S β W K ≫
        H.map (X := (op (H.obj (op K, W)), W))
          (Y := (op (H.obj (op K', W)), W))
          ((H.map (X := (op K', W)) (Y := (op K, W)) (f.op, 𝟙 W)).op, 𝟙 W) =
      f ≫ delta S β W K' := by
  let := S.monoidal
  let := β
  apply (S.transpose K (H.obj (op K', W)) W).symm.injective
  rw [uncurry_hom, uncurry_left, delta_uncurry, delta_uncurry]
  change (𝟙 K ⊗ₘ H.map (f.op, 𝟙 W)) ≫
      ((β_ K (H.obj (op K, W))).hom ≫ S.evaluation K W) =
    (f ⊗ₘ 𝟙 (H.obj (op K', W))) ≫
      ((β_ K' (H.obj (op K', W))).hom ≫ S.evaluation K' W)
  have he : (H.map (f.op, 𝟙 W) ⊗ₘ 𝟙 K) ≫ S.evaluation K W =
      (𝟙 (H.obj (op K', W)) ⊗ₘ f) ≫ S.evaluation K' W := by
    simpa [CoefficientClosedStructure.evaluation] using S.evaluation_naturality K' K W f
  simp only [BraidedCategory.braiding_naturality_assoc]
  rw [he]

end FormalLaws

section Sites

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})

variable {D : Type d} [Category.{vd} D] (J' : GrothendieckTopology D)
  [HasSheafify J' AddCommGrpCat.{max d vd s}]
  [J'.WEqualsLocallyBijective AddCommGrpCat.{max d vd s}]
  (R' : Sheaf J' CommRingCat.{max d vd s})
  (U : RingedTensorModules.{c, v, r} J R ⥤ RingedTensorModules.{d, vd, s} J' R')
  [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]

variable [HasDerivedCategory.{wb} (RingedTensorModules.{c, v, r} J R)]
  [HasDerivedCategory.{wa} (RingedTensorModules.{d, vd, s} J' R')]
  [∀ I : Type (max c v r), PreservesLimitsOfShape (Discrete I) U]
  [U.PreservesKInjectiveComplexes]
  (u : Underived.{c, v, r, d, vd, s} J R J' R' U)
  (SB : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, wb} J R))
  (TB : CoefficientTensorModels.{r, c, v, wb} J R SB)
  (βB : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, r} J R))
    _ SB.monoidal)
  (cB : RingedDerivedTensorCoherence.{c, v, r, wb} J R SB TB βB)
  (SA : CoefficientClosedStructure (derivedInternalHomOfUniverses.{d, vd, s, wa} J' R'))
  (TA : CoefficientTensorModels.{s, d, vd, wa} J' R' SA)
  (βA : @SymmetricCategory (DerivedCategory (RingedTensorModules.{d, vd, s} J' R'))
    _ SA.monoidal)
  (cA : RingedDerivedTensorCoherence.{d, vd, s, wa} J' R' SA TA βA)
  (χ : RingedForgetTwoInjective.Comparison.{wb, wa, c, v, r, d, vd, s}
    J R J' R' U u.hom)

end Sites
end CategoryTheory.RingedForgetTensorTransposition

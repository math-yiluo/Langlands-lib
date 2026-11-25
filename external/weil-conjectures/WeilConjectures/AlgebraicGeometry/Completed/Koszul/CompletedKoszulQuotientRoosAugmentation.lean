/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Koszul.KoszulReconstructionModels
public import WeilConjectures.CategoryTheory.ExactProductsRoos.ExactProductsRoosComparisonSupplement
import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulTensorQuotientConeProZero
import WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicRoosProZeroCone
import WeilConjectures.AlgebraicGeometry.ProEtaleCountableProductsExact
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import Mathlib.CategoryTheory.Sites.CompatibleSheafification
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism

/-! # The strict completed Koszul-to-quotient Roos augmentation

Source: Stacks Project, Tags 091N and 099M
(blueprint: lem-weil-pbc-completed-koszul-quotient-roos-augmentation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

section FibreMaps

variable {B : Type*} [Category B] [Abelian B]
  {X Y X' Y' X'' Y'' : CochainComplex B ℤ}
  {f : X ⟶ Y} {g : X' ⟶ Y'} {h : X'' ⟶ Y''}

private def fibreArrowMap (α : Arrow.mk f ⟶ Arrow.mk g) :
    CochainComplex.mappingCocone f ⟶ CochainComplex.mappingCocone g :=
  (HomologicalComplex.homotopyCofiber.mapArrowHom f g
    (fun j : ℤ ↦ ⟨j - 1, sub_add_cancel j 1⟩) α)⟦(-1 : ℤ)⟧'

private theorem fibreArrowMap_comp
    (α : Arrow.mk f ⟶ Arrow.mk g) (β : Arrow.mk g ⟶ Arrow.mk h) :
    fibreArrowMap (α ≫ β) = fibreArrowMap α ≫ fibreArrowMap β := by
  dsimp only [fibreArrowMap]
  rw [← (shiftFunctor _ (-1 : ℤ)).map_comp,
    ← HomologicalComplex.homotopyCofiber.mapArrowHom_comp]

private theorem fibreArrowMap_inlX (α : Arrow.mk f ⟶ Arrow.mk g) (p : ℤ) :
    HomologicalComplex.homotopyCofiber.inlX f p (p + (-1))
        (by change p + (-1) + 1 = p; omega) ≫ (fibreArrowMap α).f p =
      α.left.f p ≫ HomologicalComplex.homotopyCofiber.inlX g p (p + (-1))
        (by change p + (-1) + 1 = p; omega) := by
  dsimp only [fibreArrowMap]
  rw [CochainComplex.shiftFunctor_map_f',
    HomologicalComplex.homotopyCofiber.mapArrowHom,
    HomologicalComplex.homotopyCofiber.inlX_desc_f]
  simp only [Homotopy.trans_hom, Homotopy.ofEq_hom, Homotopy.compLeft_hom,
    Pi.zero_apply, zero_add, add_zero]
  rw [HomologicalComplex.homotopyCofiber.inrCompHomotopy_hom _ _ p (p + (-1))
    (by change p + (-1) + 1 = p; omega)]

private theorem fibreArrowMap_quasiIso_of_eq {f' : X ⟶ Y} (e : f = f')
    (α : Arrow.mk f ⟶ Arrow.mk g) (β : Arrow.mk f' ⟶ Arrow.mk g)
    (hl : α.left = β.left) (hr : α.right = β.right)
    (hβ : QuasiIso (fibreArrowMap β)) : QuasiIso (fibreArrowMap α) := by
  subst f'
  have hα : α = β := by
    apply Arrow.hom_ext <;> assumption
  rwa [hα]

private theorem roosDifference_ofOpSequence [HasCountableProducts B]
    (S : ℕ → CochainComplex B ℤ) (s : ∀ n, S (n + 1) ⟶ S n) :
    ExactProductsRoos.difference.app
        ((HomologicalComplex.functorEquivalence B (.up ℤ) ℕᵒᵖ).inverse.obj
          (Functor.ofOpSequence s)) = towerTransitionEndomorphism s := by
  change towerTransitionEndomorphism
      (fun n ↦ (Functor.ofOpSequence s).map (homOfLE (Nat.le_succ n)).op) = _
  congr 1
  funext n
  exact Functor.ofOpSequence_map_homOfLE_succ s n

end FibreMaps

section Assembly

variable (T : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)

private instance roosAbLocallyBijective :
    (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{t + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{t, 0} T

private theorem koszulTower_difference (r : ℕ) (a : Fin r → A)
    (P : CochainComplex (CompletedAdicModules T d) ℤ) :
    ExactProductsRoos.difference.app ((completedKoszulTensorTower T d r a).obj P) =
      completedAdicKoszulOneSubShift T d r a P := by
  exact roosDifference_ofOpSequence (completedAdicKoszulTensor T d r a P)
    (completedAdicKoszulTensorStep T d r a P)

private theorem koszulTower_productMap (r : ℕ) (a : Fin r → A)
    {P P' : CochainComplex (CompletedAdicModules T d) ℤ} (f : P ⟶ P') :
    ExactProductsRoos.product.map ((completedKoszulTensorTower T d r a).map f) =
      reconstructionKoszulProductMap T d r a f := rfl

private def augmentationArrow (r : ℕ) (a : Fin r → A)
    (β : completedKoszulTensorTower T d r a ⟶
      (completedAdicOrdinaryTower T d).mapHomologicalComplex (.up ℤ))
    (P : CochainComplex (CompletedAdicModules T d) ℤ) :
    Arrow.mk (-completedAdicKoszulOneSubShift T d r a P) ⟶
      Arrow.mk (-ExactProductsRoos.difference.app
        (((completedAdicOrdinaryTower T d).mapHomologicalComplex (.up ℤ)).obj P)) where
  left := ExactProductsRoos.product.map (β.app P)
  right := ExactProductsRoos.product.map (β.app P)
  w := by
    rw [← koszulTower_difference]
    exact (ExactProductsRoos.arrowMap (β.app P)).w

private def roosAugmentation (r : ℕ) (a : Fin r → A)
    (β : completedKoszulTensorTower T d r a ⟶
      (completedAdicOrdinaryTower T d).mapHomologicalComplex (.up ℤ)) :
    reconstructionKoszulFiberFunctor T d r a ⟶
      (completedAdicOrdinaryTower T d).mapHomologicalComplex (.up ℤ) ⋙
        ExactProductsRoos.fibre where
  app P := fibreArrowMap (augmentationArrow T d r a β P)
  naturality P P' f := by
    let δ : Arrow.mk (-completedAdicKoszulOneSubShift T d r a P) ⟶
        Arrow.mk (-completedAdicKoszulOneSubShift T d r a P') :=
      { left := reconstructionKoszulProductMap T d r a f
        right := reconstructionKoszulProductMap T d r a f
        w := reconstructionKoszulProductMap_comm T d r a f }
    have h : δ ≫ augmentationArrow T d r a β P' =
        augmentationArrow T d r a β P ≫ ExactProductsRoos.arrowMap
          (((completedAdicOrdinaryTower T d).mapHomologicalComplex (.up ℤ)).map f) := by
      apply Arrow.hom_ext
      all_goals
        change reconstructionKoszulProductMap T d r a f ≫
            ExactProductsRoos.product.map (β.app P') =
          ExactProductsRoos.product.map (β.app P) ≫ ExactProductsRoos.product.map _
        rw [← koszulTower_productMap, ← ExactProductsRoos.product.map_comp,
          β.naturality f, ExactProductsRoos.product.map_comp]
    change fibreArrowMap δ ≫ fibreArrowMap (augmentationArrow T d r a β P') =
      fibreArrowMap (augmentationArrow T d r a β P) ≫ fibreArrowMap
        (ExactProductsRoos.arrowMap
          (((completedAdicOrdinaryTower T d).mapHomologicalComplex (.up ℤ)).map f))
    rw [← fibreArrowMap_comp, ← fibreArrowMap_comp, h]

private theorem roosAugmentation_quasiIso (r : ℕ) (a : Fin r → A)
    (β : completedKoszulTensorTower T d r a ⟶
      (completedAdicOrdinaryTower T d).mapHomologicalComplex (.up ℤ))
    (P : CochainComplex (CompletedAdicModules T d) ℤ)
    (hv : ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m), DerivedCategory.Q.map
      ((CochainComplex.mappingCone (β.app P)).asFunctor.map (homOfLE h).op) = 0) :
    QuasiIso ((roosAugmentation T d r a β).app P) := by
  apply fibreArrowMap_quasiIso_of_eq
    (congrArg Neg.neg (koszulTower_difference T d r a P).symm)
    (augmentationArrow T d r a β P) (ExactProductsRoos.arrowMap (β.app P)) rfl rfl
  exact completedAdicRoosMapQuasiIsoOfProZero T d (β.app P) hv

private theorem roosAugmentation_unit (r : ℕ) (a : Fin r → A)
    (β : completedKoszulTensorTower T d r a ⟶
      (completedAdicOrdinaryTower T d).mapHomologicalComplex (.up ℤ))
    (hu : ∀ (P : CochainComplex (CompletedAdicModules T d) ℤ) (n : ℕ),
      completedAdicKoszulTensorUnit T d r a P n ≫
        (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map (β.app P)).app
          (Opposite.op n) = completedQuotientTensorUnit T d P n)
    (P : CochainComplex (CompletedAdicModules T d) ℤ) :
    completedAdicKoszulUnitComplex T d r a P ≫ (roosAugmentation T d r a β).app P =
      (NatTrans.mapHomologicalComplex (reconstructionOrdinaryUnit T d) (.up ℤ)).app P ≫
        ExactProductsRoos.comparison.app
          (((completedAdicOrdinaryTower T d).mapHomologicalComplex (.up ℤ)).obj P) := by
  have hprod : completedAdicKoszulProductUnit T d r a P ≫
        ExactProductsRoos.product.map (β.app P) =
      (NatTrans.mapHomologicalComplex (reconstructionOrdinaryUnit T d) (.up ℤ)).app P ≫
        ExactProductsRoos.inclusion.app
          (((completedAdicOrdinaryTower T d).mapHomologicalComplex (.up ℤ)).obj P) := by
    apply Limits.Pi.hom_ext
    intro n
    have hn := hu P n
    change completedAdicKoszulTensorUnit T d r a P n ≫ _ = _ at hn
    simp only [completedAdicKoszulProductUnit, ExactProductsRoos.product,
      Category.assoc, Limits.Pi.map_π, Limits.Pi.lift_comp_π]
    change (Limits.Pi.lift (completedAdicKoszulTensorUnit T d r a P) ≫
      Limits.Pi.π (completedAdicKoszulTensor T d r a P) n) ≫ _ = _
    rw [Limits.Pi.lift_comp_π]
    exact hn
  ext p : 1
  dsimp only [HomologicalComplex.comp_f, completedAdicKoszulUnitComplex, roosAugmentation]
  rw [Category.assoc, fibreArrowMap_inlX]
  dsimp only [augmentationArrow, Arrow.Hom.left]
  change _ = _ ≫ (ExactProductsRoos.comparisonApp _).f p
  rw [ExactProductsRoos.comparisonApp_f]
  simpa only [HomologicalComplex.comp_f, Category.assoc] using congrArg
    (fun f ↦ f.f p ≫ HomologicalComplex.homotopyCofiber.inlX
      (-ExactProductsRoos.difference.app
        (((completedAdicOrdinaryTower T d).mapHomologicalComplex (.up ℤ)).obj P))
      p (p + (-1)) (by change p + (-1) + 1 = p; omega)) hprod

end Assembly

/-- The coefficient augmentation induces a natural chain map of the explicit Roos
models. It is a quasi-isomorphism on unbounded K-flat complexes and preserves the actual
zero-second-coordinate quotient unit.

Source: Stacks Project, Tags 091N, 099M; the strict augmentation part of blueprint
sec-proper-base-change/sk-thm-properbasechange, order 1248
(blueprint: lem-weil-pbc-completed-koszul-quotient-roos-augmentation).
Proof: augment the exterior Koszul complex on the powers a_i^(m+1) to A/I^(m+1).
Its degree-zero component is the quotient map and its negative components vanish.
These maps commute with the inverse diagonal Koszul transitions and quotient maps.
Sheafify and extend scalars to the completed ring. Finite coefficient identification
identifies the targets with the recorded finite coefficient module sheaves. Tensor
with C, form the maps of products, and take the induced maps of mapping fibres of
minus one-minus-transition; this constructs the stated natural chain map. The strict
augmentation cone is pro-zero in the derived category by Noetherian Koszul pro-zero
and the cofinality of generator-power ideals with I-powers. Constant sheafification is
exact and completed scalar extension is flat. Tensor by K-flat C preserves these
quasi-isomorphisms and derived-zero transition maps. Exact countable products identify
its Roos fibre with the derived inverse limit, which kills a pro-zero tower; the fibre
map is therefore a quasi-isomorphism. Every augmentation sends the exterior degree-zero
unit to the quotient of one. Taking products preserves this equation; the second
coordinate is zero throughout. This gives the asserted chain-level unit equation. -/
theorem completedKoszulQuotientRoosAugmentation
    (T : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal) :
    ∃ α : reconstructionKoszulFiberFunctor T d r a ⟶
        (completedAdicOrdinaryTower T d).mapHomologicalComplex (.up ℤ) ⋙
          ExactProductsRoos.fibre,
      (∀ (P : CochainComplex (CompletedAdicModules T d) ℤ),
        CochainComplex.IsAcyclicTensorKFlat (R := completedAdicCommRing T d) P →
          QuasiIso (α.app P)) ∧
      (∀ P : CochainComplex (CompletedAdicModules T d) ℤ,
        completedAdicKoszulUnitComplex T d r a P ≫ α.app P =
          (NatTrans.mapHomologicalComplex (reconstructionOrdinaryUnit T d) (.up ℤ)).app P ≫
            ExactProductsRoos.comparison.app
              (((completedAdicOrdinaryTower T d).mapHomologicalComplex (.up ℤ)).obj P)) := by
  obtain ⟨β, ⟨hu, hz⟩, _⟩ := completedKoszulTensorQuotientAugmentation T d r a ha
  refine ⟨roosAugmentation T d r a β, ?_, roosAugmentation_unit T d r a β hu⟩
  intro P hP
  exact roosAugmentation_quasiIso T d r a β P
    (completedKoszulTensorQuotientConeProZero T d r a ha β hu hz P hP)

end AlgebraicGeometry.Scheme

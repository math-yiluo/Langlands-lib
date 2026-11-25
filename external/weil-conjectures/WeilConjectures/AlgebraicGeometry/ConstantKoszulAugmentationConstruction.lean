/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionCore
import all WeilConjectures.CategoryTheory.TensorQuotientAugmentation

/-! # Constructing a normalized tower augmentation from low-degree data

Source: Stacks Project, Tag 099M, strict Koszul quotient augmentation.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace CategoryTheory.ConstantCompletion
variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
variable (A : Type u) [CommRing A] (I : Ideal A) (b : Bool)
variable (r : ℕ) (a : Fin r → A)

private def quotientReductionUnit (n : ℕ) :
    𝟭 (Mod (coefficients J A I b)) ⟶ reduction J A I b n where
  app M := ((reductionUnit J A I b).app M).app (op n)
  naturality _ _ f := congrArg (fun k ↦ k.app (op n))
    ((reductionUnit J A I b).naturality f)

@[irreducible] private def quotientAugmentation
    (e₀ : ∀ n : ℕ, ((ringedKoszulDualTower (coefficients J A I b) r
      (fun i ↦ algebraSection (baseMap J A I b) (a i))).obj (op n)).X 0 ≅
        SheafOfModules.unit (siteModuleRings (coefficients J A I b)))
    (hz : let := SheafOfModules.monoidalCategory (coefficients J A I b)
      ∀ (n : ℕ) (M : Mod (coefficients J A I b)),
        M ◁ (((ringedKoszulDualTower (coefficients J A I b) r
          (fun i ↦ algebraSection (baseMap J A I b) (a i))).obj (op n)).d (-1) 0 ≫
            (e₀ n).hom) ≫ (ρ_ M).hom ≫
              ((reductionUnit J A I b).app M).app (op n) = 0)
    (he : ∀ {m k : ℕᵒᵖ} (f : m ⟶ k),
      ((ringedKoszulDualTower (coefficients J A I b) r
        (fun i ↦ algebraSection (baseMap J A I b) (a i))).map f).f 0 ≫
          (e₀ k.unop).hom = (e₀ m.unop).hom) :
    ringedKoszulTensorTowerFunctor (coefficients J A I b) r
        (fun i ↦ algebraSection (baseMap J A I b) (a i)) ⟶
      (reductionTower J A I b).mapHomologicalComplex (.up ℤ) := by
  let O := coefficients J A I b
  let s := fun i ↦ algebraSection (baseMap J A I b) (a i)
  let D := ringedKoszulDualTower O r s
  let := SheafOfModules.monoidalCategory O
  let := SheafOfModules.symmetricCategory O
  let := Classical.choice (SheafOfModules.tensorClosed O).1
  let := Classical.choice (SheafOfModules.tensorClosed O).2.1
  let η := quotientReductionUnit J A I b
  let c (P : Cx O) (t : ℤ) (n : ℕᵒᵖ) :=
    quotientTensorComponent P (D.obj n) (e₀ n.unop)
      (reduction J A I b n.unop) (η n.unop) t
  exact complexNatTransOfComponents (ringedKoszulTensorTowerFunctor O r s)
    ((reductionTower J A I b).mapHomologicalComplex (.up ℤ)) c
    (by
      intro P t m k f
      let τ : reduction J A I b m.unop ⟶ reduction J A I b k.unop :=
        (Functor.ofOpSequence (reductionStep J A I b)).map f
      have hη : η m.unop ≫ τ = η k.unop := by
        apply NatTrans.ext
        funext M
        exact (((reductionUnit J A I b).app M).naturality f).symm
      exact quotientTensorComponent_transition P (D.obj m) (D.obj k)
        (e₀ m.unop) (e₀ k.unop) (D.map f) (he f)
        (reduction J A I b m.unop) (reduction J A I b k.unop)
        (η m.unop) (η k.unop) τ hη t)
    (by
      intro P t k htk n
      have hk : t + 1 = k := htk
      subst k
      simp only [ringedKoszulTensorTowerFunctor, ringedKoszulTensorTowerComplex,
        Functor.mapHomologicalComplex_obj_d, CochainComplex.of_d,
        Functor.whiskerLeft_app, HomologicalComplex.dNatTrans_app]
      exact quotientTensorComponent_comm P (D.obj n) (e₀ n.unop)
        (reduction J A I b n.unop) (η n.unop) (hz n.unop) t)
    (by
      intro P P' f t n
      exact quotientTensorComponent_naturality P P' (D.obj n) (e₀ n.unop)
        (reduction J A I b n.unop) (η n.unop) f t)

private theorem quotientAugmentation_f
    (e₀ : ∀ n : ℕ, ((ringedKoszulDualTower (coefficients J A I b) r
      (fun i ↦ algebraSection (baseMap J A I b) (a i))).obj (op n)).X 0 ≅
        SheafOfModules.unit (siteModuleRings (coefficients J A I b)))
    (hz : let := SheafOfModules.monoidalCategory (coefficients J A I b)
      ∀ (n : ℕ) (M : Mod (coefficients J A I b)),
        M ◁ (((ringedKoszulDualTower (coefficients J A I b) r
          (fun i ↦ algebraSection (baseMap J A I b) (a i))).obj (op n)).d (-1) 0 ≫
            (e₀ n).hom) ≫ (ρ_ M).hom ≫
              ((reductionUnit J A I b).app M).app (op n) = 0)
    (he : ∀ {m k : ℕᵒᵖ} (f : m ⟶ k),
      ((ringedKoszulDualTower (coefficients J A I b) r
        (fun i ↦ algebraSection (baseMap J A I b) (a i))).map f).f 0 ≫
          (e₀ k.unop).hom = (e₀ m.unop).hom)
    (P : Cx (coefficients J A I b)) (t : ℤ) (n : ℕᵒᵖ) :
    let O := coefficients J A I b
    let := SheafOfModules.monoidalCategory O
    let := SheafOfModules.symmetricCategory O
    let := Classical.choice (SheafOfModules.tensorClosed O).1
    let := Classical.choice (SheafOfModules.tensorClosed O).2.1
    (((quotientAugmentation J A I b r a e₀ hz he).app P).f t).app n =
      quotientTensorComponent P
        ((ringedKoszulDualTower O r
          (fun i ↦ algebraSection (baseMap J A I b) (a i))).obj n)
        (e₀ n.unop) (reduction J A I b n.unop)
        (quotientReductionUnit J A I b n.unop) t := by
  unfold quotientAugmentation
  rfl

/-- A degree-zero identification compatible with the dual unit and transitions,
and annihilation of the incoming differential after reduction, determine a normalized
strict tower augmentation.
Source: Stacks Project, Tag 099M, Koszul quotient construction.
(auxiliary; not a blueprint node).

Proof: on each total-tensor summand of Koszul degree zero use its identification
with the coefficient unit, the right unitor and the actual reduction unit. Send
other summands to zero. Coproduct descent and the incoming-differential hypothesis
give the cochain equation. Transition compatibility and naturality give a strict
tower map natural in the complex. The inverse right-unitor formula computes its
composite with the tensor unit. Evaluate the ordinary-limit map at each projection
and use the uniqueness characterization of ordinaryUnit to obtain its unit law.
The other normalization law is the zero formula on the remaining summands. -/
theorem constantKoszulAugmentationFromLowDegrees
    (e₀ : ∀ n : ℕ, ((ringedKoszulDualTower (coefficients J A I b) r
      (fun i ↦ algebraSection (baseMap J A I b) (a i))).obj (op n)).X 0 ≅
        SheafOfModules.unit (siteModuleRings (coefficients J A I b)))
    (hz : let := SheafOfModules.monoidalCategory (coefficients J A I b)
      ∀ (n : ℕ) (M : Mod (coefficients J A I b)),
        M ◁ (((ringedKoszulDualTower (coefficients J A I b) r
          (fun i ↦ algebraSection (baseMap J A I b) (a i))).obj (op n)).d (-1) 0 ≫
            (e₀ n).hom) ≫ (ρ_ M).hom ≫
              ((reductionUnit J A I b).app M).app (op n) = 0)
    (he : ∀ {m k : ℕᵒᵖ} (f : m ⟶ k),
      ((ringedKoszulDualTower (coefficients J A I b) r
        (fun i ↦ algebraSection (baseMap J A I b) (a i))).map f).f 0 ≫
          (e₀ k.unop).hom = (e₀ m.unop).hom)
    (hu : ∀ n : ℕ,
      (ringedKoszulDualUnit (coefficients J A I b) r
        (fun i ↦ algebraSection (baseMap J A I b) (a i)) n).f 0 ≫ (e₀ n).hom =
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0
            (SheafOfModules.unit (siteModuleRings (coefficients J A I b)))).hom) :
    ∃ α : ringedKoszulTensorTowerFunctor (coefficients J A I b) r
        (fun i ↦ algebraSection (baseMap J A I b) (a i)) ⟶
      (reductionTower J A I b).mapHomologicalComplex (.up ℤ),
  (∀ P : Cx (coefficients J A I b),
    ringedKoszulLimitUnit (coefficients J A I b) r
        (fun i ↦ algebraSection (baseMap J A I b) (a i)) P ≫
      (ordinaryLimit (coefficients J A I b)).map (α.app P) = ordinaryUnit J A I b P) ∧
  (∀ (P : Cx (coefficients J A I b)) (n : ℕ) (p q : ℤ), q ≠ 0 →
    HomologicalComplex.ιMapBifunctor P
        ((ringedKoszulDualTower (coefficients J A I b) r
          (fun i ↦ algebraSection (baseMap J A I b) (a i))).obj (op n))
        (@MonoidalCategory.curriedTensor _ _
          (SheafOfModules.monoidalCategory (coefficients J A I b)))
        (.up ℤ) p q (p + q) rfl ≫ ((α.app P).f (p + q)).app (op n) = 0) := by
  let O := coefficients J A I b
  let s := fun i ↦ algebraSection (baseMap J A I b) (a i)
  let D := ringedKoszulDualTower O r s
  let := SheafOfModules.monoidalCategory O
  let := SheafOfModules.symmetricCategory O
  let := Classical.choice (SheafOfModules.tensorClosed O).1
  let := Classical.choice (SheafOfModules.tensorClosed O).2.1
  let η := quotientReductionUnit J A I b
  let α := quotientAugmentation J A I b r a e₀ hz he
  refine ⟨α, ?_, ?_⟩
  · intro P
    apply (ordinaryUnit_existsUnique J A I b P).unique ?_
      (ordinaryUnit_existsUnique J A I b P).exists.choose_spec
    intro t n
    change (ringedKoszulLimitUnitF O r s P t ≫
      limMap ((α.app P).f t)) ≫ limit.π _ (op n) = _
    rw [Category.assoc, limMap_π, ← Category.assoc]
    dsimp only [α]
    rw [quotientAugmentation_f]
    change (limit.lift _ (ringedKoszulTensorUnitCone O r s P t) ≫
      limit.π _ (op n)) ≫ quotientTensorComponent P (D.obj (op n)) (e₀ n)
        (reduction J A I b n) (η n) t = _
    rw [limit.lift_π]
    exact quotientTensorComponent_unit P (D.obj (op n)) (e₀ n)
      (ringedKoszulDualUnit O r s n) (hu n) (reduction J A I b n) (η n) t
  · intro P n p q hq
    dsimp only [α]
    rw [quotientAugmentation_f]
    exact quotientTensorComponent_ι_zero P (D.obj (op n)) (e₀ n)
      (reduction J A I b n) (η n) p q (p + q) rfl hq

end CategoryTheory.ConstantCompletion

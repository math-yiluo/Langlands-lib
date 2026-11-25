/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits

import Mathlib.LinearAlgebra.Contraction
import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence

/-! # Natural dual comparison for constant finite free sheaves -/

@[expose] public section
universe u
open CategoryTheory MonoidalCategory Limits
namespace AlgebraicGeometry.Scheme

/-- Sheafification of the componentwise monoidal constant-presheaf functor. -/
private noncomputable local instance (X : Scheme.{u}) {Λ : Type (u + 1)} [CommRing Λ] :
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).Monoidal := by
  letI : (Functor.const X.Etaleᵒᵖ (C := ModuleCat.{u + 1} Λ)).Monoidal :=
    Functor.CoreMonoidal.toMonoidal
      { εIso := Iso.refl _, μIso A B := NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
          intros; simp)
        μIso_hom_natural_left := by intros; ext; simp
        μIso_hom_natural_right := by intros; ext; simp
        associativity := by intros; ext; simp
        left_unitality := by intros; ext; simp
        right_unitality := by intros; ext; simp }
  unfold constantSheaf
  infer_instance

open TensorProduct

-- The following contraction calculations follow the dual-basis proof in
-- WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed.
-- We retain the explicit pairing, so no arbitrary dualizable witness is chosen.
/-- Evaluation of a coefficient vector against its linear dual. -/
private def coefficientDualEvaluation {Λ : Type (u + 1)} [CommRing Λ]
    (M : ModuleCat.{u + 1} Λ) :
    M ⊗ ModuleCat.of Λ (M →ₗ[Λ] Λ) ⟶ 𝟙_ (ModuleCat.{u + 1} Λ) :=
  ModuleCat.ofHom (TensorProduct.lift (LinearMap.id.flip))

/-- The comparison obtained by sheafifying coefficient evaluation and currying. -/
private noncomputable def constantModuleDualComparison (X : Scheme.{u})
    {Λ : Type (u + 1)} [CommRing Λ] (M : ModuleCat.{u + 1} Λ) :
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
      (ModuleCat.of Λ (M →ₗ[Λ] Λ)) ⟶
    (ihom ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)).obj
      (𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :=
  MonoidalClosed.curry
    ((Functor.Monoidal.μIso (constantSheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} Λ)) M (ModuleCat.of Λ (M →ₗ[Λ] Λ))).hom ≫
      (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map
        (coefficientDualEvaluation M) ≫
      (Functor.Monoidal.εIso (constantSheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} Λ))).inv)

private theorem coefficientDualEvaluation_natural {Λ : Type (u + 1)} [CommRing Λ]
    {M N : ModuleCat.{u + 1} Λ} (g : M ⟶ N) :
    g ▷ ModuleCat.of Λ (N →ₗ[Λ] Λ) ≫ coefficientDualEvaluation N =
      M ◁ ModuleCat.ofHom g.hom.dualMap ≫ coefficientDualEvaluation M := by
  ext : 1
  apply TensorProduct.ext'
  intro x f
  rfl

private theorem constantModuleDualComparison_natural (X : Scheme.{u})
    {Λ : Type (u + 1)} [CommRing Λ] {M N : ModuleCat.{u + 1} Λ} (g : M ⟶ N) :
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map
      (ModuleCat.ofHom g.hom.dualMap) ≫ constantModuleDualComparison X M =
    constantModuleDualComparison X N ≫
      (MonoidalClosed.pre ((constantSheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} Λ)).map g)).app
          (𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) := by
  unfold constantModuleDualComparison
  rw [← MonoidalClosed.curry_natural_left, MonoidalClosed.curry_pre_app]
  congr 1
  simp only [Functor.Monoidal.μIso_hom,
    Functor.LaxMonoidal.μ_natural_left_assoc, Functor.LaxMonoidal.μ_natural_right_assoc]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc,
    coefficientDualEvaluation_natural]

/-- The coordinate dual basis gives an exact pairing, including the empty basis. -/
@[instance_reducible]
private noncomputable def finiteFreePairing {Λ : Type (u + 1)} [CommRing Λ]
    (n : ℕ) : ExactPairing (ModuleCat.of Λ (Fin n → Λ))
      (ModuleCat.of Λ ((Fin n → Λ) →ₗ[Λ] Λ)) := by
  let M := Fin n → Λ
  let ξ : Fin n → Module.Dual Λ M := fun j ↦ LinearMap.proj j
  let m : Fin n → M := fun j ↦ Pi.single j 1
  have h (q : M) : ∑ j, ξ j q • m j = q := by
    ext i
    change (∑ j : Fin n, q j • Pi.single j (1 : Λ)) i = q i
    simp [Finset.sum_apply, Pi.single_apply]
  exact
    { coevaluation' := ModuleCat.ofHom (LinearMap.toSpanSingleton Λ _
        (∑ j, m j ⊗ₜ[Λ] ξ j))
      evaluation' := ModuleCat.ofHom (contractLeft Λ M)
      coevaluation_evaluation' := by
        have hz :
            (contractLeft Λ M).rTensor (Module.Dual Λ M) ∘ₗ
                (TensorProduct.assoc Λ _ _ _).symm.toLinearMap ∘ₗ
              (LinearMap.toSpanSingleton Λ _ (∑ j, m j ⊗ₜ[Λ] ξ j)).lTensor (Module.Dual Λ M) =
            (TensorProduct.lid Λ _).symm.toLinearMap ∘ₗ
              (TensorProduct.rid Λ _).toLinearMap := by
          refine TensorProduct.ext' fun φ r ↦ ?_
          simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
            LinearMap.lTensor_tmul, LinearMap.toSpanSingleton_apply, TensorProduct.rid_tmul,
            TensorProduct.lid_symm_apply, tmul_smul, map_smul]
          simp only [tmul_sum, map_sum, TensorProduct.assoc_symm_tmul,
            LinearMap.rTensor_tmul, contractLeft_apply]
          have hφ : ∑ j, φ (m j) • ξ j = φ := by
            apply LinearMap.ext
            intro (q : M)
            simp only [LinearMap.sum_apply, LinearMap.smul_apply]
            conv_rhs => rw [← h q, map_sum]
            refine Finset.sum_congr rfl fun j _ ↦ ?_
            rw [map_smul, smul_eq_mul, mul_comm, smul_eq_mul]
          conv_rhs => rw [← hφ, tmul_sum]
          congr 1
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          rw [← smul_tmul, smul_eq_mul, mul_one]
        ext : 1
        exact hz
      evaluation_coevaluation' := by
        have hz :
            (contractLeft Λ M).lTensor M ∘ₗ (TensorProduct.assoc Λ _ _ _).toLinearMap ∘ₗ
                (LinearMap.toSpanSingleton Λ _ (∑ j, m j ⊗ₜ[Λ] ξ j)).rTensor M =
              (TensorProduct.rid Λ M).symm.toLinearMap ∘ₗ
                (TensorProduct.lid Λ M).toLinearMap := by
          refine TensorProduct.ext' fun r q ↦ ?_
          simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
            LinearMap.rTensor_tmul, LinearMap.toSpanSingleton_apply, TensorProduct.lid_tmul,
            TensorProduct.rid_symm_apply, ← smul_tmul', map_smul, sum_tmul, map_sum,
            TensorProduct.assoc_tmul, LinearMap.lTensor_tmul, contractLeft_apply]
          conv_rhs => rw [← h q, sum_tmul]
          congr 1
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          rw [smul_tmul, smul_eq_mul, mul_one]
        ext : 1
        exact hz }


/-- Sheafification transports the explicit pairing; its curried evaluation is invertible. -/
private theorem constantFiniteFreeDualComparison_isIso (X : Scheme.{u})
    {Λ : Type (u + 1)} [CommRing Λ] (n : ℕ) :
    IsIso (constantModuleDualComparison X (ModuleCat.of Λ (Fin n → Λ))) := by
  let M := ModuleCat.of Λ (Fin n → Λ)
  let D := ModuleCat.of Λ ((Fin n → Λ) →ₗ[Λ] Λ)
  let : ExactPairing M D := finiteFreePairing n
  let : ExactPairing D M := BraidedCategory.exactPairing_swap M D
  let C := constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  let : ExactPairing (C.obj D) (C.obj M) := ExactPairing.map C D M
  have he : ε_ D M = coefficientDualEvaluation M := by
    ext : 1
    apply TensorProduct.ext'
    intro x f
    rfl
  change IsIso (MonoidalClosed.curry _)
  have hev : ε_ (C.obj D) (C.obj M) =
      (Functor.Monoidal.μIso C M D).hom ≫ C.map (coefficientDualEvaluation M) ≫
        (Functor.Monoidal.εIso C).inv := by
    change Functor.LaxMonoidal.μ C M D ≫ C.map (ε_ D M) ≫
      Functor.OplaxMonoidal.η C = _
    rw [he]
    rfl
  rw [← hev]
  infer_instance

/-- Constant sheafification identifies the duals of finite free modules naturally.

Source: `WeilConjectures/ConstructibleSheaf/Monoidal.lean`,
`IsFiniteLocallyConstantSheaf.ihom_unit` docstring, finite free transpose step.

Proof: Write Λ^n as the finite biproduct of n copies of Λ. Constant sheafification
preserves this biproduct and identifies the constant coefficient module with the
monoidal unit. Internal Hom into the unit takes this finite biproduct to the
finite product of n copies of the unit, using the tensor-Hom adjunction and the
unit constraints. The dual basis identifies Hom(Λ^n, Λ) with that same product.
Compose these comparisons to obtain e_n. For a matrix g, precomposition on
internal Hom sends a functional with coordinates a_i to the coordinates
sum_i g_ij a_i: evaluate on each basis vector and use linearity. The coefficient
dual map has exactly the same coordinates, so its constant sheaf map commutes
with e_n and e_m. Equality is detected by the finite product projections.
For n = 0 or m = 0 these are empty products and the same equations hold;
no noetherian hypothesis or assertion about an infinite product is used.
(blueprint: lem-constant-finite-free-dual-naturality) -/
theorem constantFiniteFreeDualNaturality
    (X : Scheme.{u}) {Λ : Type (u + 1)} [CommRing Λ] :
    ∃ e : ∀ n : ℕ,
      (MonoidalClosed.internalHom.flip.obj
        (𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))).obj
          (Opposite.op ((constantSheaf X.smallEtaleTopology
            (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ (Fin n → Λ)))) ≅
        (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
          (ModuleCat.of Λ ((Fin n → Λ) →ₗ[Λ] Λ)),
      ∀ (n m : ℕ) (g : (Fin m → Λ) →ₗ[Λ] (Fin n → Λ)),
        ((MonoidalClosed.internalHom.flip.obj
          (𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))).map
            ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map
              (ModuleCat.ofHom g)).op) ≫ (e m).hom =
          (e n).hom ≫
            (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map
              (ModuleCat.ofHom g.dualMap) := by
  let C := constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  let a (n : ℕ) := constantModuleDualComparison X (ModuleCat.of Λ (Fin n → Λ))
  have (n : ℕ) : IsIso (a n) := constantFiniteFreeDualComparison_isIso X n
  refine ⟨fun n ↦ (asIso (a n)).symm, ?_⟩
  intro n m g
  apply (cancel_epi (a n)).mp
  simp only [Iso.symm_hom, asIso_inv, IsIso.hom_inv_id_assoc]
  have h := constantModuleDualComparison_natural X (ModuleCat.ofHom g)
  change C.map (ModuleCat.ofHom g.dualMap) ≫ a m =
    a n ≫ _ at h
  change (a n ≫ (MonoidalClosed.pre (C.map (ModuleCat.ofHom g))).app
    (𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))) ≫ inv (a m) =
      C.map (ModuleCat.ofHom g.dualMap)
  rw [← h]
  simp

end AlgebraicGeometry.Scheme

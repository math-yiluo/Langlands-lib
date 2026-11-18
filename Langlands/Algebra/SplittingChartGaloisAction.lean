import Langlands.Algebra.MatrixGaloisCocycle
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Actual Galois descent action supplied by an algebra splitting chart -/

noncomputable section
universe u
open scoped TensorProduct
open Matrix

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.CentralSimple

variable {k L A : Type u} [Field k] [Field L] [Algebra k L]
  [Ring A] [Algebra k A]

/-- The actual coefficient action on the scalar-extended algebra. -/
def tensorCoefficientMap (σ : L ≃ₐ[k] L) : L ⊗[k] A →ₐ[k] L ⊗[k] A :=
  Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id k A)

@[simp] theorem tensorCoefficientMap_tmul (σ : L ≃ₐ[k] L) (l : L) (a : A) :
    tensorCoefficientMap (A := A) σ (l ⊗ₜ[k] a) = σ l ⊗ₜ[k] a := by
  simp [tensorCoefficientMap]

@[simp] theorem tensorCoefficientMap_one (X : L ⊗[k] A) :
    tensorCoefficientMap (A := A) 1 X = X := by
  induction X with
  | tmul l a => simp
  | add X Y hX hY => simp only [map_add, hX, hY]

@[simp] theorem tensorCoefficientMap_mul (σ τ : L ≃ₐ[k] L) (X : L ⊗[k] A) :
    tensorCoefficientMap (A := A) (σ * τ) X =
      tensorCoefficientMap σ (tensorCoefficientMap τ X) := by
  induction X with
  | tmul l a => simp only [tensorCoefficientMap_tmul, AlgEquiv.mul_apply]
  | add X Y hX hY => simp only [map_add, hX, hY]

/-- A splitting chart transports the actual coefficient action to matrices. -/
def splittingChartAction {n : ℕ}
    (e : L ⊗[k] A ≃ₐ[L] Matrix (Fin n) (Fin n) L) :
    SemilinearGaloisAction k L (Matrix (Fin n) (Fin n) L) where
  act σ := ((e.restrictScalars k).toAlgHom.comp
    ((tensorCoefficientMap σ).comp (e.symm.restrictScalars k).toAlgHom)).toRingHom
  act_algebraMap σ l := by
    change e (tensorCoefficientMap σ (e.symm (algebraMap L _ l))) = _
    rw [e.symm.commutes]
    have hscalar : tensorCoefficientMap (A := A) σ (algebraMap L (L ⊗[k] A) l) =
        algebraMap L (L ⊗[k] A) (σ l) := by
      change tensorCoefficientMap σ (l ⊗ₜ[k] (1 : A)) = σ l ⊗ₜ[k] (1 : A)
      exact tensorCoefficientMap_tmul σ l 1
    rw [hscalar, e.commutes]
  act_one X := by
    change e (tensorCoefficientMap 1 (e.symm X)) = X
    rw [tensorCoefficientMap_one, e.apply_symm_apply]
  act_mul σ τ X := by
    change e (tensorCoefficientMap (σ * τ) (e.symm X)) =
      e (tensorCoefficientMap σ (e.symm (e (tensorCoefficientMap τ (e.symm X)))))
    rw [e.symm_apply_apply, tensorCoefficientMap_mul]

/-- The transported action remembers the supplied splitting chart on every tensor. -/
theorem splittingChartAction_apply {n : ℕ}
    (e : L ⊗[k] A ≃ₐ[L] Matrix (Fin n) (Fin n) L)
    (σ : L ≃ₐ[k] L) (X : L ⊗[k] A) :
    (splittingChartAction e).act σ (e X) = e (tensorCoefficientMap σ X) := by
  change e (tensorCoefficientMap σ (e.symm (e X))) = _
  rw [e.symm_apply_apply]

/-- The original algebra maps into the actual fixed matrix algebra of its splitting chart. -/
def splittingChartFixedHom {n : ℕ}
    (e : L ⊗[k] A ≃ₐ[L] Matrix (Fin n) (Fin n) L) :
    A →ₐ[k] (splittingChartAction e).fixed :=
  AlgHom.codRestrict
    ((e.restrictScalars k).toAlgHom.comp Algebra.TensorProduct.includeRight)
    (splittingChartAction e).fixed (fun a σ => by
      change (splittingChartAction e).act σ (e (1 ⊗ₜ[k] a)) = e (1 ⊗ₜ[k] a)
      rw [splittingChartAction_apply, tensorCoefficientMap_tmul, map_one])

/-- The actual original-algebra inclusion into the fixed matrix algebra is injective. -/
theorem splittingChartFixedHom_injective {n : ℕ}
    (e : L ⊗[k] A ≃ₐ[L] Matrix (Fin n) (Fin n) L) :
    Function.Injective (splittingChartFixedHom e) := by
  intro a b h
  have hv := congrArg Subtype.val h
  change e (1 ⊗ₜ[k] a) = e (1 ⊗ₜ[k] b) at hv
  exact Algebra.TensorProduct.includeRight_injective (RingHom.injective (algebraMap k L))
    (e.injective hv)

variable [FiniteDimensional k L] [IsGalois k L] [FiniteDimensional k A]

/-- The fixed matrix algebra of the chart has the exact dimension of the original algebra. -/
theorem finrank_splittingChart_fixed {n : ℕ}
    (e : L ⊗[k] A ≃ₐ[L] Matrix (Fin n) (Fin n) L) :
    Module.finrank k (splittingChartAction e).fixed = Module.finrank k A := by
  calc
    Module.finrank k (splittingChartAction e).fixed =
        Module.finrank L (L ⊗[k] (splittingChartAction e).fixed) := Module.finrank_baseChange.symm
    _ = Module.finrank L (Matrix (Fin n) (Fin n) L) :=
      (splittingChartAction e).descentEquiv.toLinearEquiv.finrank_eq
    _ = Module.finrank k A := e.toLinearEquiv.finrank_eq.symm.trans Module.finrank_baseChange

/-- The supplied splitting chart identifies the original algebra with its actual
Galois-fixed matrix algebra. -/
def splittingChartFixedEquiv {n : ℕ}
    (e : L ⊗[k] A ≃ₐ[L] Matrix (Fin n) (Fin n) L) :
    A ≃ₐ[k] (splittingChartAction e).fixed := by
  let : FiniteDimensional k (splittingChartAction e).fixed :=
    (splittingChartAction e).finiteDimensional_fixed
  apply AlgEquiv.ofBijective (splittingChartFixedHom e)
  exact ⟨splittingChartFixedHom_injective e,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (finrank_splittingChart_fixed e).symm
      (f := (splittingChartFixedHom e).toLinearMap)).mp (splittingChartFixedHom_injective e)⟩

end Langlands.CentralSimple

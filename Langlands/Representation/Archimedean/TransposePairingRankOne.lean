import Langlands.Representation.Archimedean.TransposePairing
import Langlands.Representation.Archimedean.GKModuleDensity
import Mathlib.LinearAlgebra.Dual.Lemmas

noncomputable section

universe uV

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped TensorProduct Matrix

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The bilinear square of a linear functional. -/
def squareFunctionalPairing (ℓ : Module.Dual ℂ V) : V →ₗ[ℂ] V →ₗ[ℂ] ℂ where
  toFun v := (ℓ v) • ℓ
  map_add' v w := by simp [add_smul]
  map_smul' c v := by simp [smul_smul]

@[simp]
theorem squareFunctionalPairing_apply (ℓ : Module.Dual ℂ V) (v w : V) :
    squareFunctionalPairing ℓ v w = ℓ v * ℓ w := rfl

namespace TransposePairingRankOne

variable (𝕂 : Type) [RCLike 𝕂]

lemma matrix_mul_comm (X Y : Matrix (Fin 1) (Fin 1) 𝕂) : X * Y = Y * X := by
  ext i j
  fin_cases i
  fin_cases j
  simp [Matrix.mul_apply, mul_comm]

omit [RCLike 𝕂] in
lemma matrix_transpose (X : Matrix (Fin 1) (Fin 1) 𝕂) : X.transpose = X := by
  ext i j
  fin_cases i
  fin_cases j
  rfl

lemma compact_conj (k : Matrix.unitaryGroup (Fin 1) 𝕂)
    (X : Matrix (Fin 1) (Fin 1) 𝕂) :
    (k : Matrix (Fin 1) (Fin 1) 𝕂) * X * star (k : Matrix (Fin 1) (Fin 1) 𝕂) = X := by
  rw [matrix_mul_comm 𝕂 (k : Matrix (Fin 1) (Fin 1) 𝕂) X, Matrix.mul_assoc,
    (mul_eq_one_comm.mpr (Matrix.UnitaryGroup.star_mul_self k)), mul_one]

lemma compactIota_eq_inv (k : Matrix.unitaryGroup (Fin 1) 𝕂) :
    compactIota 𝕂 1 k = k⁻¹ := by
  apply Subtype.ext
  exact matrix_transpose 𝕂 _

lemma complexifiedMatrixLieIota_eq_neg (X : ℂ ⊗[ℝ] Matrix (Fin 1) (Fin 1) 𝕂) :
    complexifiedMatrixLieIota 𝕂 1 X = -X := by
  induction X using TensorProduct.inductionOn with
  | tmul c X => rw [complexifiedMatrixLieIota_tmul, matrix_transpose, TensorProduct.tmul_neg]
  | add X Y hX hY => simp only [map_add, hX, hY, neg_add]

lemma lie_eq_zero (X Y : ℂ ⊗[ℝ] Matrix (Fin 1) (Fin 1) 𝕂) : ⁅X, Y⁆ = 0 := by
  induction X using TensorProduct.inductionOn with
  | tmul c X =>
    induction Y using TensorProduct.inductionOn with
    | tmul d Y =>
      have h : ⁅X, Y⁆ = 0 := by
        change X * Y - Y * X = 0
        rw [matrix_mul_comm 𝕂 X Y, sub_self]
      simp [LieAlgebra.ExtendScalars.bracket_tmul, h]
    | add Y Z hY hZ =>
      rw [@LieRing.lie_add _
        (LieAlgebra.ExtendScalars.instLieRing ℝ ℂ (Matrix (Fin 1) (Fin 1) 𝕂)),
        hY, hZ, add_zero]
  | add X Z hX hZ =>
    rw [@LieRing.add_lie _
      (LieAlgebra.ExtendScalars.instLieRing ℝ ℂ (Matrix (Fin 1) (Fin 1) 𝕂)),
      hX, hZ, add_zero]

variable {𝕂}
  (ρ : Representation ℂ (Matrix.unitaryGroup (Fin 1) 𝕂) V)
  (π : (ℂ ⊗[ℝ] Matrix (Fin 1) (Fin 1) 𝕂) →ₗ⁅ℂ⁆ Module.End ℂ V)
  (hcov : ∀ (k : Matrix.unitaryGroup (Fin 1) 𝕂)
      (X : Matrix (Fin 1) (Fin 1) 𝕂) (v : V),
    ρ k (π (1 ⊗ₜ[ℝ] X) v) =
      π (1 ⊗ₜ[ℝ] ((k : Matrix (Fin 1) (Fin 1) 𝕂) * X *
        star (k : Matrix (Fin 1) (Fin 1) 𝕂))) (ρ k v))

include hcov in
lemma rep_lie_commute (k : Matrix.unitaryGroup (Fin 1) 𝕂)
    (X : ℂ ⊗[ℝ] Matrix (Fin 1) (Fin 1) 𝕂) (v : V) :
    ρ k (π X v) = π X (ρ k v) := by
  induction X using TensorProduct.inductionOn with
  | tmul c X =>
    have hc : (c ⊗ₜ[ℝ] X : ℂ ⊗[ℝ] Matrix (Fin 1) (Fin 1) 𝕂) =
        c • (1 ⊗ₜ[ℝ] X) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hc, map_smul, LinearMap.smul_apply, map_smul, LinearMap.smul_apply,
      hcov, compact_conj]
  | add X Y hX hY => simp only [map_add, LinearMap.add_apply, hX, hY]

lemma rep_commute (k l : Matrix.unitaryGroup (Fin 1) 𝕂) (v : V) :
    ρ k (ρ l v) = ρ l (ρ k v) := by
  have h : k * l = l * k := Subtype.ext (matrix_mul_comm 𝕂 _ _)
  rw [← Module.End.mul_apply, ← map_mul, h, map_mul, Module.End.mul_apply]

lemma lie_commute (X Y : ℂ ⊗[ℝ] Matrix (Fin 1) (Fin 1) 𝕂) (v : V) :
    π X (π Y v) = π Y (π X v) := by
  have h := π.map_lie X Y
  rw [lie_eq_zero, map_zero] at h
  have h' : π X * π Y - π Y * π X = 0 := h.symm
  exact LinearMap.congr_fun (sub_eq_zero.mp h') v

include hcov in
/-- Schur's lemma makes both actions scalar in matrix size one. -/
lemma scalar_actions (h : GKModuleDensity.Hyp ρ π) :
    (∀ k, ∃ c : ℂ, ∀ v, ρ k v = c • v) ∧
    (∀ X, ∃ c : ℂ, ∀ v, π X v = c • v) := by
  constructor
  · intro k
    exact GKModuleDensity.exists_eq_scalar h (ρ k)
      (rep_commute ρ k) (rep_lie_commute ρ π hcov k)
  · intro X
    exact GKModuleDensity.exists_eq_scalar h (π X)
      (fun k v => (rep_lie_commute ρ π hcov k X v).symm) (lie_commute π X)

include hcov in
/-- A nonzero functional gives the actual inverse-transpose pairing at rank one. -/
theorem hasNonzeroTransposeGKPairing (h : GKModuleDensity.Hyp ρ π) :
    HasNonzeroTransposeGKPairing 𝕂 1 ρ π := by
  have := h.irreducible.1
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨ℓ, hℓ⟩ := Module.Projective.exists_dual_eq_one ℂ hv
  obtain ⟨hK, hL⟩ := scalar_actions ρ π hcov h
  refine ⟨squareFunctionalPairing ℓ, ⟨?_, ?_⟩, ?_⟩
  · intro k y x
    rw [compactIota_eq_inv]
    obtain ⟨c, hc⟩ := hK k
    have he : c • ρ k⁻¹ x = x := by
      rw [← hc, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel,
        map_one, Module.End.one_apply]
    change ℓ (ρ k y) * ℓ (ρ k⁻¹ x) = ℓ y * ℓ x
    rw [hc y, map_smul, smul_eq_mul]
    calc c * ℓ y * ℓ (ρ k⁻¹ x) = ℓ y * (c * ℓ (ρ k⁻¹ x)) := by ring
      _ = ℓ y * ℓ (c • ρ k⁻¹ x) := by rw [map_smul, smul_eq_mul]
      _ = ℓ y * ℓ x := by rw [he]
  · intro X y x
    obtain ⟨c, hc⟩ := hL X
    rw [complexifiedMatrixLieIota_eq_neg, map_neg, LinearMap.neg_apply, hc y, hc x]
    simp [squareFunctionalPairing_apply, mul_left_comm]
  · intro h0
    have e := LinearMap.congr_fun (LinearMap.congr_fun h0 v) v
    simp [hℓ] at e

end TransposePairingRankOne

/-- The exact real transpose-pairing conclusion in matrix size one. -/
theorem realTransposePairing_rankOne
    (ρ : Representation ℂ (Matrix.unitaryGroup (Fin 1) ℝ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin 1) (Fin 1) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V)
    (hgk : IsRealGKModule 1 ρ π) (hirr : IsIrreducibleGKModule ρ π)
    (hadm : IsAdmissibleGKModule ρ) :
    HasNonzeroTransposeGKPairing ℝ 1 ρ π := by
  apply TransposePairingRankOne.hasNonzeroTransposeGKPairing ρ π hgk.2.2.2
  exact ⟨hirr, hadm, fun v => ⟨FiniteVectors.orbitSpan ρ v,
    FiniteVectors.self_mem_orbitSpan ρ v, hgk.1 v,
    fun k w hw => (FiniteVectors.orbitSubrepresentation ρ v).apply_mem_toSubmodule k hw⟩,
    hgk.2.1⟩

/-- The exact complex transpose-pairing conclusion in matrix size one. -/
theorem complexTransposePairing_rankOne
    (ρ : Representation ℂ (Matrix.unitaryGroup (Fin 1) ℂ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin 1) (Fin 1) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V)
    (hgk : IsComplexGKModule 1 ρ π) (hirr : IsIrreducibleGKModule ρ π)
    (hadm : IsAdmissibleGKModule ρ) :
    HasNonzeroTransposeGKPairing ℂ 1 ρ π := by
  apply TransposePairingRankOne.hasNonzeroTransposeGKPairing ρ π hgk.2.2.2
  exact ⟨hirr, hadm, fun v => ⟨FiniteVectors.orbitSpan ρ v,
    FiniteVectors.self_mem_orbitSpan ρ v, hgk.1 v,
    fun k w hw => (FiniteVectors.orbitSubrepresentation ρ v).apply_mem_toSubmodule k hw⟩,
    hgk.2.1⟩

end Langlands.Archimedean

import Langlands.Shimura.Unitary.FiniteModels
import Langlands.Algebra.MatrixAlgEquivInnerProof
import Langlands.LinearAlgebra.SpecialLinearHermitianNormalization

/-! # Hermitian coordinates for second-kind matrix involutions -/

noncomputable section

namespace Langlands.Shimura.FiniteUnitary

open Langlands.GroupScheme
open Langlands.LinearAlgebra.SpecialLinearHermitianNormalization

variable {R L : Type*} [CommRing R] [Field L] [Algebra R L] {n : ℕ}
  (c : AlgebraInvolution R L)

local notation "M" => Matrix (Fin n) (Fin n) L
local notation "θ" => matrixTranspose c n

private theorem transpose_algebraMap (a : L) :
    θ (algebraMap L M a) = algebraMap L M (c a) := by
  ext i j
  change c ((algebraMap L M a) j i) = (algebraMap L M (c a)) i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.algebraMap_matrix_apply]
  · simp [Matrix.algebraMap_matrix_apply, hij, Ne.symm hij]

private def composedInvolutions (ρ : AlgebraInvolution R M)
    (hρ : ∀ a : L, ρ (algebraMap L M a) = algebraMap L M (c a)) : M ≃ₐ[L] M where
  toFun X := ρ (θ X)
  invFun X := θ (ρ X)
  left_inv X := by simp
  right_inv X := by simp
  map_add' X Y := by simp
  map_mul' X Y := by simp
  commutes' a := by
    rw [transpose_algebraMap, hρ, c.apply_apply]

private def coefficientInvolution : SU3Root.RingInvolution L where
  bar :=
    { toFun := c
      invFun := c
      left_inv := c.apply_apply
      right_inv := c.apply_apply
      map_add' := c.apply_add
      map_mul' a b := (c.apply_mul a b).trans (mul_comm _ _) }
  involutive := c.apply_apply

private theorem transpose_smul (a : L) (X : M) : θ (a • X) = c a • θ X := by
  rw [Algebra.smul_def, Algebra.smul_def, (θ).apply_mul, transpose_algebraMap, Algebra.commutes]

/-- An involution inducing nontrivial coefficient conjugation on a full matrix
algebra has an invertible Hermitian Gram matrix for its adjoint description. -/
theorem exists_hermitianGram_of_matrixInvolution (hn : 0 < n)
    (hc : ∃ a : L, c a ≠ a) (ρ : AlgebraInvolution R M)
    (hρ : ∀ a : L, ρ (algebraMap L M a) = algebraMap L M (c a)) :
    ∃ H : Mˣ, ∃ hH : θ (H : M) = H, ∀ X : M, ρ X = (θ).adjoint H hH X := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨U, hU⟩ := Langlands.MatrixAlgebra.exists_unit_conj_of_algEquiv
    (composedInvolutions c ρ hρ)
  have hu (X : M) : ρ X = (U : M) * θ X * (↑U⁻¹ : M) := by
    simpa only [composedInvolutions, AlgEquiv.coe_mk, Equiv.coe_fn_mk, (θ).apply_apply]
      using hU (θ X)
  have hh (X : Mˣ) : ρ.units X = U * (θ).units X * U⁻¹ := Units.ext (hu X)
  let D := U * ((θ).units U)⁻¹
  have hD (X : Mˣ) : D * X * D⁻¹ = X := by
    calc
      _ = ρ.units (ρ.units X) := by
        rw [hh (ρ.units X), hh X, (θ).units_mul, (θ).units_mul, (θ).units_inv, (θ).units_units]
        dsimp only [D]
        group
      _ = X := ρ.units_units X
  have hcen : D ∈ Subgroup.center (Matrix.GeneralLinearGroup (Fin n) L) := by
    apply Subgroup.mem_center_iff.mpr
    intro X
    have he := congrArg (fun Y : Mˣ => Y * D) (hD X)
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using he.symm
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hcen
  obtain ⟨a, ha⟩ := hcen
  let J := U⁻¹
  have hJunit : (θ).units J = Matrix.GeneralLinearGroup.scalar (Fin n) a * J := by
    calc
      _ = J * D := by
        change (θ).units U⁻¹ = U⁻¹ * (U * ((θ).units U)⁻¹)
        rw [(θ).units_inv, ← mul_assoc, inv_mul_cancel, one_mul]
      _ = _ := by
        rw [← ha]
        exact Units.ext (Algebra.commutes (a : L) (J : M)).symm
  have hJ : θ (J : M) = (a : L) • (J : M) := by
    change ((θ).units J : M) = _
    rw [hJunit, Units.val_mul, Algebra.smul_def]
    rfl
  have hab : c (a : L) * (a : L) = 1 := by
    have h := congrArg θ hJ
    rw [(θ).apply_apply, transpose_smul, hJ, smul_smul] at h
    apply smul_left_injective L (Units.ne_zero J)
    simpa only [one_smul] using h.symm
  obtain ⟨b, hb⟩ := exists_hermitian_scaling_unit (coefficientInvolution c) hc (a : L) hab
  change c (b : L) * (a : L) = (b : L) at hb
  let B := Units.map (algebraMap L M).toMonoidHom b
  let H := B * J
  have hself : θ (H : M) = (H : M) := by
    change θ (algebraMap L M (b : L) * (J : M)) =
      algebraMap L M (b : L) * (J : M)
    rw [(θ).apply_mul, transpose_algebraMap, hJ, Algebra.smul_def]
    calc
      _ = algebraMap L M (c (b : L)) * (algebraMap L M (a : L) * (J : M)) :=
        (Algebra.commutes _ _).symm
      _ = _ := by rw [← mul_assoc, ← map_mul, hb]
  refine ⟨H, hself, fun X => ?_⟩
  have hcancel : (↑B⁻¹ : M) * θ X * (B : M) = θ X := by
    have hc' : θ X * (B : M) = (B : M) * θ X :=
      (Algebra.commutes (b : L) (θ X)).symm
    rw [mul_assoc, hc', ← mul_assoc, Units.inv_mul, one_mul]
  rw [AlgebraInvolution.adjoint_apply, hu]
  change (U : M) * θ X * (↑U⁻¹ : M) =
    (↑((B * J)⁻¹ : Mˣ) : M) * θ X * (↑(B * J) : M)
  rw [_root_.mul_inv_rev, Units.val_mul, Units.val_mul]
  change (↑J⁻¹ : M) * θ X * (J : M) =
    (↑J⁻¹ : M) * (↑B⁻¹ : M) * θ X * ((B : M) * (J : M))
  rw [show (↑J⁻¹ : M) * (↑B⁻¹ : M) * θ X * ((B : M) * (J : M)) =
    (↑J⁻¹ : M) * ((↑B⁻¹ : M) * θ X * (B : M)) * (J : M) by simp only [mul_assoc], hcancel]

/-- The Hermitian Gram matrix and the corresponding adjoint formula. -/
def hermitianGramOfMatrixInvolution (hn : 0 < n) (hc : ∃ a : L, c a ≠ a)
    (ρ : AlgebraInvolution R M)
    (hρ : ∀ a : L, ρ (algebraMap L M a) = algebraMap L M (c a)) :
    {H : Mˣ // ∃ hH : θ (H : M) = H, ∀ X : M, ρ X = (θ).adjoint H hH X} :=
  ⟨_, Classical.choose_spec (exists_hermitianGram_of_matrixInvolution c hn hc ρ hρ)⟩

end Langlands.Shimura.FiniteUnitary

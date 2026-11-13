import Langlands.Representation.RankinSelberg.DualModels
import Langlands.Representation.Conductor.EssentialDualSetup
import Langlands.Representation.Conductor.SphericalPolynomial
import Langlands.Representation.RankinSelberg.SymmetricAlternantBridge

/-!
# Dual transforms of coefficients and of spherical Whittaker functions

The first dual transform `W ↦ W(w₀ ᵗg⁻¹)` of the coefficient of `v` for a functional `ℓ`
is the coefficient of `v` for the dual functional of the inverse-transpose pullback.
The second dual transform of Jacquet's spherical function `W(g; x; ψ̄)` is
`W(g; x⁻¹; ψ)`, the spherical function for `ψ.scale (-1)` at the inverse parameters.
-/

noncomputable section

namespace Langlands.Conductor

open Langlands.GeneralLinear Langlands.Whittaker Langlands.HarmonicAnalysis
open Langlands.RankinSelberg
open Langlands.GeneralLinear.Iwasawa Langlands.GeneralLinear.Spherical

universe uF uV

section Cells

variable {F : Type uF} [Field F] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  {v : Valuation F Γ₀} {n : ℕ} {ϖ : Fˣ} (hϖ : IsUniformizingElement v ϖ)
  (θ : upperUnipotent (n + 1) F →* ℂˣ)

/-- A cell function depends only on its values at antitone exponents. -/
theorem cellFunction_congr {c c' : (Fin (n + 1) → ℤ) → ℂ}
    (h : ∀ lam, Antitone lam → c lam = c' lam) :
    cellFunction hϖ θ c = cellFunction hϖ θ c' := by
  funext g
  unfold cellFunction
  split_ifs with hg
  · rw [h _ hg]
  · rfl

/-- The long Weyl element is integral. -/
theorem weylLong_mem_integralSubgroup_of_valuation :
    weylLong (n + 1) F ∈ integralSubgroup v.integer n := by
  rw [mem_integralSubgroup]
  have hent : ∀ i j : Fin (n + 1), weylLong (n + 1) F i j ∈ v.integer := by
    intro i j
    rw [weylLong_entry]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  refine ⟨hent, fun i j => ?_⟩
  rw [weylLong_inv]
  exact hent i j

/-- Inverse transposition preserves `GL_(n+1)(O)`. -/
theorem inverseTranspose_mem_integralSubgroup_of_valuation
    {k : Langlands.GeneralLinear (n + 1) F} (hk : k ∈ integralSubgroup v.integer n) :
    inverseTranspose (n + 1) F k ∈ integralSubgroup v.integer n := by
  rw [mem_integralSubgroup] at hk ⊢
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [inverseTranspose_entry]
    exact hk.2 j i
  · rw [← map_inv, inverseTranspose_entry, inv_inv]
    exact hk.1 j i

omit [LinearOrderedCommGroupWithZero Γ₀] in
/-- Conjugation by the long Weyl element reverses a torus element. -/
theorem weylLong_mul_torus_mul_weylLong (lam : Fin (n + 1) → ℤ) :
    weylLong (n + 1) F * torus ϖ lam * weylLong (n + 1) F =
      torus ϖ (fun i => lam (Fin.rev i)) := by
  apply Units.ext
  ext i j
  rw [weylLong_conjugate_entry]
  change (torus ϖ lam).val i.rev j.rev = (torus ϖ (fun i => lam (Fin.rev i))).val i j
  rw [torus_val, torus_val, Matrix.diagonal_apply, Matrix.diagonal_apply]
  simp only [Fin.rev_inj]

omit [LinearOrderedCommGroupWithZero Γ₀] in
/-- Inverse transposition inverts a torus element. -/
theorem inverseTranspose_torus_eq (lam : Fin (n + 1) → ℤ) :
    inverseTranspose (n + 1) F (torus ϖ lam) = torus ϖ (fun i => -lam i) := by
  apply Units.ext
  rw [inverseTranspose_coe, torus_inv_val, Matrix.diagonal_transpose, torus_val]
  congr 1
  funext i
  rw [zpow_neg]

end Cells

/-! ### Weights reversed and negated -/

section Weights

variable {n : ℕ}

/-- The weight `-w₀ lam`, `i ↦ -lam (n - i)`. -/
def dualWeight (lam : Fin (n + 1) → ℤ) : Fin (n + 1) → ℤ :=
  fun i => -lam (Fin.rev i)

theorem antitone_dualWeight_iff (lam : Fin (n + 1) → ℤ) :
    Antitone (dualWeight lam) ↔ Antitone lam := by
  constructor
  · intro h i j hij
    have := h (Fin.rev_le_rev.mpr hij)
    simp only [dualWeight, Fin.rev_rev, neg_le_neg_iff] at this
    exact this
  · intro h i j hij
    have := h (Fin.rev_le_rev.mpr hij)
    simp only [dualWeight, neg_le_neg_iff]
    exact this

theorem halfModulus_dualWeight (q : ℕ) (lam : Fin (n + 1) → ℤ) :
    halfModulus q (dualWeight lam) = halfModulus q lam := by
  unfold halfModulus
  congr 1
  congr 1
  rw [← Equiv.sum_comp Fin.revPerm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [dualWeight, Fin.revPerm_apply, Fin.rev_rev, Fin.val_rev]
  have hi := i.isLt
  rw [show n + 1 - ((i : ℕ) + 1) = n - i by omega, Nat.cast_sub (by omega : (i : ℕ) ≤ n)]
  ring

end Weights

/-! ### Schur functions at inverse parameters -/

section SchurInversion

open MvPolynomial

variable {n : ℕ}

/-- Column scaling and row reversal turn the weight-`γ` alternant at inverse parameters
into the alternant of the weight `i ↦ γ 0 - γ (n - i)`. -/
theorem sign_mul_eval_inv_alternant (γ : Fin (n + 1) → ℤ) (hγ : ∀ i, 0 ≤ γ i)
    (hanti : Antitone γ) (y : Fin (n + 1) → ℂ) (hy : ∀ k, y k ≠ 0) :
    ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (n + 1))) : ℤ) : ℂ) *
      ((∏ k, y k) ^ (γ 0 + n) * eval (fun k => (y k)⁻¹) (alternantMatrix ℂ γ).det) =
      eval y (alternantMatrix ℂ (fun i => γ 0 - γ (Fin.rev i))).det := by
  set Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
    Matrix.of fun i k => y k ^ (γ 0 - γ i + i) with hQ
  have hdetQ : Q.det = (∏ k, y k) ^ (γ 0 + n) *
      eval (fun k => (y k)⁻¹) (alternantMatrix ℂ γ).det := by
    rw [RingHom.map_det, ← Finset.prod_zpow, ← Matrix.det_mul_row]
    congr 1
    apply Matrix.ext
    intro i k
    have hi := i.isLt
    have hnn : 0 ≤ γ i - (i : ℤ) + n := by have := hγ i; omega
    simp only [hQ, Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply, alternantMatrix,
      eval_pow, eval_X, inv_pow]
    rw [← zpow_natCast, Int.toNat_of_nonneg hnn, ← zpow_neg, ← zpow_add₀ (hy k)]
    congr 1
    ring
  rw [← hdetQ, ← Matrix.det_permute, RingHom.map_det]
  congr 1
  apply Matrix.ext
  intro i k
  have hi := i.add_rev_cast
  have hle : γ (Fin.rev i) ≤ γ 0 := hanti (Fin.zero_le _)
  have hnn : 0 ≤ γ 0 - γ (Fin.rev i) - (i : ℤ) + n := by omega
  simp only [hQ, Matrix.of_apply, Matrix.submatrix_apply, Fin.revPerm_apply, id_eq,
    RingHom.mapMatrix_apply, Matrix.map_apply, alternantMatrix, eval_pow, eval_X]
  rw [← zpow_natCast, Int.toNat_of_nonneg hnn]
  congr 1
  omega

/-- The cross-multiplied inversion identity at one tuple of nonzero parameters. -/
theorem jacobiTrudi_inv_mul_baseAlternant (α : Fin (n + 1) → ℤ) (hα : ∀ i, 0 ≤ α i)
    (hanti : Antitone α) (y : Fin (n + 1) → ℂ) (hy : ∀ k, y k ≠ 0) :
    (∏ k, y k) ^ α 0 * eval (fun k => (y k)⁻¹) (jacobiTrudi ℂ α) *
        eval y (alternantMatrix ℂ (0 : Fin (n + 1) → ℤ)).det =
      eval y (jacobiTrudi ℂ (fun i => α 0 - α (Fin.rev i))) *
        eval y (alternantMatrix ℂ (0 : Fin (n + 1) → ℤ)).det := by
  have hP : (∏ k, y k) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hy k
  have hβ : ∀ i, 0 ≤ α 0 - α (Fin.rev i) := fun i => sub_nonneg.mpr (hanti (Fin.zero_le _))
  have h1 := sign_mul_eval_inv_alternant α hα hanti y hy
  have h0 := sign_mul_eval_inv_alternant (0 : Fin (n + 1) → ℤ) (fun _ => le_rfl)
    (fun _ _ _ => le_rfl) y hy
  have hz : (fun i : Fin (n + 1) =>
      (0 : Fin (n + 1) → ℤ) 0 - (0 : Fin (n + 1) → ℤ) (Fin.rev i)) = 0 := by
    funext i
    simp
  rw [hz] at h0
  simp only [Pi.zero_apply, zero_add] at h0
  have h2 := congrArg (eval fun k => (y k)⁻¹) (jacobiTrudi_mul_baseAlternant (R := ℂ) α hα)
  have h3 := congrArg (eval y) (jacobiTrudi_mul_baseAlternant (R := ℂ) _ hβ)
  rw [map_mul] at h2 h3
  rw [zpow_add₀ hP] at h1
  linear_combination (-((∏ k, y k) ^ α 0 * eval (fun k => (y k)⁻¹) (jacobiTrudi ℂ α))) * h0 +
    (((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (n + 1))) : ℤ) : ℂ) *
      (∏ k, y k) ^ α 0 * (∏ k, y k) ^ (n : ℤ)) * h2 + h1 - h3

/-- Inverting the parameters of the Jacobi–Trudi polynomial of an antitone nonnegative
weight `α`: `(∏ x) ^ α 0 · s_α(x⁻¹) = s_β(x)` with `β i = α 0 - α (n - i)`. -/
theorem prod_zpow_mul_eval_inv_jacobiTrudi (α : Fin (n + 1) → ℤ) (hα : ∀ i, 0 ≤ α i)
    (hanti : Antitone α) (x : Fin (n + 1) → ℂˣ) :
    (∏ k, (x k : ℂ)) ^ α 0 * eval (fun k => ((x k : ℂ))⁻¹) (jacobiTrudi ℂ α) =
      eval (fun k => (x k : ℂ)) (jacobiTrudi ℂ (fun i => α 0 - α (Fin.rev i))) := by
  have hprod : (∏ i : Fin (n + 1), (X i : MvPolynomial (Fin (n + 1)) ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => X_ne_zero i
  have hM := powers_le_nonZeroDivisors_of_noZeroDivisors hprod
  have : IsDomain (TorusPolynomialAlgebra (Fin (n + 1)) ℂ) :=
    IsLocalization.isDomain_localization hM
  have hunit : ∀ k, IsUnit (algebraMap (MvPolynomial (Fin (n + 1)) ℂ)
      (TorusPolynomialAlgebra (Fin (n + 1)) ℂ) (X k)) := fun k =>
    isUnit_of_dvd_unit (map_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ k)))
      (IsLocalization.Away.algebraMap_isUnit _)
  obtain ⟨f, hev⟩ : ∃ f : TorusPolynomialAlgebra (Fin (n + 1)) ℂ,
      ∀ y : Fin (n + 1) → ℂˣ, torusPolynomialEvaluation (Fin (n + 1)) ℂ y f =
        (∏ k, (y k : ℂ)) ^ α 0 * eval (fun k => ((y k : ℂ))⁻¹) (jacobiTrudi ℂ α) := by
    refine ⟨((torusDeterminantUnit (Fin (n + 1)) ℂ ^ α 0 :
        (TorusPolynomialAlgebra (Fin (n + 1)) ℂ)ˣ) : TorusPolynomialAlgebra (Fin (n + 1)) ℂ) *
      aeval (fun k => (((hunit k).unit⁻¹ : (TorusPolynomialAlgebra (Fin (n + 1)) ℂ)ˣ) :
        TorusPolynomialAlgebra (Fin (n + 1)) ℂ)) (jacobiTrudi ℂ α), fun y => ?_⟩
    rw [map_mul, algHom_apply_unit_zpow, torusPolynomialEvaluation_determinantUnit,
      comp_aeval_apply]
    simp only [Units.val_zpow_eq_zpow_val, Units.coe_prod, map_units_inv, IsUnit.unit_spec,
      torusPolynomialEvaluation_algebraMap, aeval_X, aeval_eq_eval]
  have hinj := IsLocalization.injective (TorusPolynomialAlgebra (Fin (n + 1)) ℂ) hM
  have ha0 : algebraMap (MvPolynomial (Fin (n + 1)) ℂ) (TorusPolynomialAlgebra (Fin (n + 1)) ℂ)
      (alternantMatrix ℂ (0 : Fin (n + 1) → ℤ)).det ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ hinj, ← det_erasedCoefficientMatrix]
    exact det_erasedCoefficientMatrix_ne_zero n
  have hmul : f * algebraMap (MvPolynomial (Fin (n + 1)) ℂ)
        (TorusPolynomialAlgebra (Fin (n + 1)) ℂ) (alternantMatrix ℂ (0 : Fin (n + 1) → ℤ)).det =
      algebraMap (MvPolynomial (Fin (n + 1)) ℂ) (TorusPolynomialAlgebra (Fin (n + 1)) ℂ)
          (jacobiTrudi ℂ (fun i => α 0 - α (Fin.rev i))) *
        algebraMap (MvPolynomial (Fin (n + 1)) ℂ) (TorusPolynomialAlgebra (Fin (n + 1)) ℂ)
          (alternantMatrix ℂ (0 : Fin (n + 1) → ℤ)).det := by
    apply torusPolynomial_eq_of_evaluations
    intro y
    rw [map_mul, map_mul, hev, torusPolynomialEvaluation_algebraMap,
      torusPolynomialEvaluation_algebraMap]
    exact jacobiTrudi_inv_mul_baseAlternant α hα hanti _ fun k => (y k).ne_zero
  have hfg := congrArg (torusPolynomialEvaluation (Fin (n + 1)) ℂ x)
    (mul_right_cancel₀ ha0 hmul)
  rw [hev, torusPolynomialEvaluation_algebraMap] at hfg
  exact hfg

/-- Schur functions at inverse parameters: `s_lam(x⁻¹) = s_(-w₀ lam)(x)` for antitone
`lam`. -/
theorem satakeSchur_inv (x : Fin (n + 1) → ℂˣ) {lam : Fin (n + 1) → ℤ} (hlam : Antitone lam) :
    satakeSchur x⁻¹ lam = satakeSchur x (dualWeight lam) := by
  set α : Fin (n + 1) → ℤ := fun i => lam i - lam (Fin.last n) with hαdef
  have hα : ∀ i, 0 ≤ α i := fun i => sub_nonneg.mpr (hlam (Fin.le_last i))
  have hanti : Antitone α := fun i j hij => sub_le_sub_right (hlam hij) _
  have key := prod_zpow_mul_eval_inv_jacobiTrudi α hα hanti x
  have hβ : (fun i => dualWeight lam i - dualWeight lam (Fin.last n)) =
      fun i => α 0 - α (Fin.rev i) := by
    funext i
    simp only [dualWeight, α, Fin.rev_last]
    ring
  have hP : (∏ i, (x i : ℂ)) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => (x i).ne_zero
  unfold satakeSchur
  rw [hβ, ← key]
  simp only [Pi.inv_apply, Units.val_inv_eq_inv_val]
  rw [Finset.prod_inv_distrib, inv_zpow', ← mul_assoc, ← zpow_add₀ hP]
  congr 2
  simp only [dualWeight, α, Fin.rev_last]
  ring

end SchurInversion

/-! ### The second dual transform of the spherical Whittaker function -/

section SecondDual

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsTopologicalRing F]
  {ψ : UnitaryAdditiveCharacter F} {n : ℕ}
  (hψ : ∀ x ∈ (ValuativeRel.valuation F).integer, ψ x = 1)
  {ϖ : Fˣ} (hϖ : IsUniformizingElement (ValuativeRel.valuation F) ϖ) (q : ℕ)

/-- Torus values of `W̃(g; x; ψ̄) = W(w₀ ᵗg⁻¹; x; ψ̄)`: at `ϖ ^ lam` it is
`δ_B ^ (1/2) (ϖ ^ lam) s_lam(x⁻¹)` for antitone `lam`, and zero otherwise. -/
theorem secondDualFunction_inverseSphericalWhittaker_torus (x : Fin (n + 1) → ℂˣ)
    (lam : Fin (n + 1) → ℤ) :
    (secondDualFunction ψ n (inverseSphericalWhittaker hψ hϖ q x)).val (torus ϖ lam) =
      if Antitone lam then halfModulus q lam * satakeSchur x⁻¹ lam else 0 := by
  have hθ := isIntegrallyTrivial_inverseStandardCharacter hψ n
  rw [secondDualFunction_apply, inverseSphericalWhittaker_apply, inverseTranspose_torus_eq]
  have hw : weylLong (n + 1) F * torus ϖ (fun i => -lam i) =
      torus ϖ (dualWeight lam) * weylLong (n + 1) F := by
    have hd : torus ϖ (dualWeight lam) =
        weylLong (n + 1) F * torus ϖ (fun i => -lam i) * weylLong (n + 1) F :=
      (weylLong_mul_torus_mul_weylLong (F := F) (ϖ := ϖ) (fun i => -lam i)).symm
    rw [hd, mul_assoc _ (weylLong (n + 1) F), weylLong_mul_self, mul_one]
  rw [hw, sphericalWhittaker_mul_integral hϖ q x hθ _ weylLong_mem_integralSubgroup_of_valuation,
    sphericalWhittaker_torus hϖ q x hθ]
  simp only [antitone_dualWeight_iff, halfModulus_dualWeight]
  split_ifs with hlam
  · rw [satakeSchur_inv x hlam]
  · rfl

/-- The second dual transform of Jacquet's `W(g; x; ψ̄)` is `W(g; x⁻¹; ψ)`, the spherical
function for `ψ.scale (-1)` (whose inverse character is the standard character of `ψ`)
at the inverse parameters. -/
theorem secondDualFunction_inverseSphericalWhittaker
    (hψ' : ∀ x ∈ (ValuativeRel.valuation F).integer, ψ.scale (-1) x = 1)
    (x : Fin (n + 1) → ℂˣ) :
    secondDualFunction ψ n (inverseSphericalWhittaker hψ hϖ q x) =
      inverseSphericalWhittaker hψ' hϖ q x⁻¹ := by
  have hθ := isIntegrallyTrivial_inverseStandardCharacter hψ n
  have hθ' := isIntegrallyTrivial_inverseStandardCharacter hψ' n
  apply Subtype.ext
  change (secondDualFunction ψ n (inverseSphericalWhittaker hψ hϖ q x)).val =
    sphericalWhittaker hϖ (inverseStandardCharacter (ψ.scale (-1)) n) q x⁻¹
  rw [eq_cellFunction hϖ hθ' (secondDualFunction ψ n (inverseSphericalWhittaker hψ hϖ q x)).property
    ?_ ?_]
  · unfold sphericalWhittaker
    apply cellFunction_congr
    intro lam hlam
    rw [secondDualFunction_inverseSphericalWhittaker_torus, ite_eq_left hlam]
  · intro g k hk
    simp only [secondDualFunction_apply, inverseSphericalWhittaker_apply, map_mul, ← mul_assoc]
    exact sphericalWhittaker_mul_integral hϖ q x hθ _
      (inverseTranspose_mem_integralSubgroup_of_valuation hk)
  · intro lam hlam
    rw [secondDualFunction_inverseSphericalWhittaker_torus, ite_eq_right hlam]

end SecondDual

end Langlands.Conductor

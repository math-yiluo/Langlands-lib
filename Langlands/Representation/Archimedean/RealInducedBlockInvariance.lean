import Langlands.Automorphic.CuspidalAdmissible.CentralEigen
import Langlands.Representation.Archimedean.RealInducedBlockBound
import Langlands.Representation.Archimedean.RealBlockLeftDerivative
import Langlands.Representation.Archimedean.RealJacquetFrobeniusProof

/-!
# Invariance of rotation averages under upper triangular block matrices

Let `φ` be a smooth function on `GL_N(ℝ)` with `φ(exp(diag x) u g) = e^{Σ αᵢ xᵢ} φ(g)` for upper
unipotent `u` (`RealBlockDerivative.IsExpEquivariant α φ`), and let `p, p + 1` be a block with
`α_p - α_{p+1} = 2`. This holds for products `u(· z₁) h(· z₂)` of a vector of a principal series
and a vector of its dual. Then the rotation average
`Φ^p_0 φ (g) = ∫₀^{2π} φ(r_p(θ) g) dθ` satisfies
`Φ^p_0 φ (b(x, y, w) g) = e^{(α_p - 1)(x + y)} Φ^p_0 φ (g)`
(`isBlockCovariant_blockFourierCoefficient_zero`). The proof differentiates along the paths
`t ↦ (1 + t v E_{p,p+1}) g` and `t ↦ exp(t diag(x, y)) g` with the Library's tridiagonal formula
`RealBlockDerivative.hasDerivAt_blockFourierCoefficient_comp` at the mode `0`: the
coefficients of the modes `±2` contain the factor `α_p - α_{p+1} - 2 = 0`.

For pairwise disjoint blocks the iterated averages satisfy
`Φ_0 ⋯ Φ_0 φ (b_1 ⋯ b_r g) = ∏_i e^{(α_{p_i} - 1)(x_i + y_i)} Φ_0 ⋯ Φ_0 φ (g)`
(`coeffs_point_mul`).
-/

noncomputable section

open scoped Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Archimedean

open Langlands.GeneralLinear

set_option backward.isDefEq.respectTransparency false

namespace RealInducedBlockInvariance

open RealBlockRotation RealBlockFourierFinite RealInducedBlockSlice RealInducedBlockBound
  RealBlockDerivative

variable {N p : ℕ}

theorem diagVec_ia (h : p + 1 < N) (x y : ℝ) : diagVec h x y (ia h) = x := by
  simp [diagVec]

theorem diagVec_ib (h : p + 1 < N) (x y : ℝ) : diagVec h x y (ib h) = y := by
  simp [diagVec, (ia_ne_ib h).symm]

theorem upperUnit_zero (h : p + 1 < N) : upperUnit h 0 = 1 := by
  apply Units.ext
  change (1 + (0 : ℝ) • Matrix.single (ia h) (ib h) (1 : ℝ)) = 1
  rw [zero_smul, add_zero]

section Invariance

variable {φ : Langlands.GeneralLinear N ℝ → ℂ}

/-- The rotation average is invariant under `1 + v E_{p,p+1}`. -/
theorem blockFourierCoefficient_zero_upperUnit_mul (h : p + 1 < N)
    (hφ : ContMDiff (matrixModel ℝ N) 𝓘(ℝ, ℂ) ∞ φ) {α : Fin N → ℂ} (hα : IsExpEquivariant α φ)
    (hδ : α (ia h) - α (ib h) = 2) (v : ℝ) (g : Langlands.GeneralLinear N ℝ) :
    blockFourierCoefficient N p 0 φ (upperUnit h v * g) = blockFourierCoefficient N p 0 φ g := by
  set E : Matrix (Fin N) (Fin N) ℝ := v • Matrix.single (ia h) (ib h) 1 with hE
  have hEE : E * E = 0 := by
    rw [hE, Matrix.smul_mul, Matrix.mul_smul, single_mul_single_self h, smul_zero, smul_zero]
  set γ : ℝ → Langlands.GeneralLinear N ℝ := fun t => upperUnit h (t * v) * g with hγ
  have hγv : ∀ t, (γ t : Matrix (Fin N) (Fin N) ℝ) =
      (1 + t • E) * (g : Matrix (Fin N) (Fin N) ℝ) := fun t => by
    rw [hγ, Units.val_mul]
    congr 1
    change 1 + (t * v) • Matrix.single (ia h) (ib h) (1 : ℝ) = 1 + t • E
    rw [hE, smul_smul]
  have e : (fun t => (γ t : Matrix (Fin N) (Fin N) ℝ)) =
      fun t : ℝ => (1 + t • E) * (g : Matrix (Fin N) (Fin N) ℝ) := funext hγv
  have hγc : ContDiff ℝ 1 fun t => (γ t : Matrix (Fin N) (Fin N) ℝ) := by
    rw [e]
    exact (contDiff_const.add (contDiff_id.smul contDiff_const)).mul contDiff_const
  have hEu : E.IsUpperTriangular := by
    intro i j hij
    simp only [hE, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
    rw [ite_eq_right (fun hc => by
      have h1 : (j : ℕ) < i := hij
      rw [← hc.1, ← hc.2] at h1
      simp [ia, ib] at h1), mul_zero]
  have hEd : ∀ i, E i i = 0 := fun i => by
    simp only [hE, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
    rw [ite_eq_right (fun hc => ia_ne_ib h (hc.1.trans hc.2.symm)), mul_zero]
  have hd : ∀ t, HasDerivAt (fun s => blockFourierCoefficient N p 0 φ (γ s)) 0 t := by
    intro t
    have hγ' : HasDerivAt (fun s => (γ s : Matrix (Fin N) (Fin N) ℝ))
        (E * (γ t : Matrix (Fin N) (Fin N) ℝ)) t := by
      rw [e]
      have hd : HasDerivAt (fun t : ℝ => (1 + t • E) * (g : Matrix (Fin N) (Fin N) ℝ))
          (E * (g : Matrix (Fin N) (Fin N) ℝ)) t := by
        simpa using (((hasDerivAt_id t).smul_const E).const_add 1).mul_const
          (g : Matrix (Fin N) (Fin N) ℝ)
      refine hd.congr_deriv ?_
      rw [hγv, ← mul_assoc, mul_add, mul_one, Matrix.mul_smul, hEE, smul_zero, add_zero]
    have := hasDerivAt_blockFourierCoefficient_comp h hφ hα hγc hEu hγ' 0
    refine this.congr_deriv ?_
    rw [hδ]
    simp [hEd]
  have hc := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv)
    1 0
  simpa only [hγ, one_mul, zero_mul, upperUnit_zero] using hc

/-- The rotation average scales by `e^{(α_p - 1)(x + y)}` under `exp(diag(x, y))`. -/
theorem blockFourierCoefficient_zero_expDiag_mul (h : p + 1 < N)
    (hφ : ContMDiff (matrixModel ℝ N) 𝓘(ℝ, ℂ) ∞ φ) {α : Fin N → ℂ} (hα : IsExpEquivariant α φ)
    (hδ : α (ia h) - α (ib h) = 2) (x y : ℝ) (g : Langlands.GeneralLinear N ℝ) :
    blockFourierCoefficient N p 0 φ (matrixExpUnit N (Matrix.diagonal (diagVec h x y)) * g) =
      Complex.exp ((α (ia h) - 1) * ((x : ℂ) + y)) * blockFourierCoefficient N p 0 φ g := by
  set L : Matrix (Fin N) (Fin N) ℝ := Matrix.diagonal (diagVec h x y) with hL
  set γ : ℝ → Langlands.GeneralLinear N ℝ := fun t => matrixExpUnit N (t • L) * g with hγ
  have hγv : ∀ t, (γ t : Matrix (Fin N) (Fin N) ℝ) =
      NormedSpace.exp (t • L) * (g : Matrix (Fin N) (Fin N) ℝ) := fun t => by
    rw [hγ, Units.val_mul, matrixExpUnit_val]
  have e : (fun t => (γ t : Matrix (Fin N) (Fin N) ℝ)) =
      fun t : ℝ => NormedSpace.exp (t • L) * (g : Matrix (Fin N) (Fin N) ℝ) := funext hγv
  have hγc : ContDiff ℝ 1 fun t => (γ t : Matrix (Fin N) (Fin N) ℝ) := by
    rw [e]
    exact ((RealJacquetFrobenius.contDiff_matExp.of_le (mod_cast le_top)).comp
      (contDiff_id.smul contDiff_const)).mul contDiff_const
  have hLu : L.IsUpperTriangular := Matrix.blockTriangular_diagonal _
  have hLd : ∀ i, L i i = diagVec h x y i := fun i => Matrix.diagonal_apply_eq _ _
  have hLpq : L (ia h) (ib h) = 0 := Matrix.diagonal_apply_ne _ (ia_ne_ib h)
  have hq : α (ib h) = α (ia h) - 2 := by rw [← hδ]; ring
  have hF : ∀ t, HasDerivAt (fun s => blockFourierCoefficient N p 0 φ (γ s))
      ((α (ia h) - 1) * ((x : ℂ) + y) * blockFourierCoefficient N p 0 φ (γ t)) t := by
    intro t
    have hγ' : HasDerivAt (fun s => (γ s : Matrix (Fin N) (Fin N) ℝ))
        (L * (γ t : Matrix (Fin N) (Fin N) ℝ)) t := by
      rw [e]
      refine ((hasDerivAt_exp_smul_const' (𝕂 := ℝ) L t).mul_const
        (g : Matrix (Fin N) (Fin N) ℝ)).congr_deriv ?_
      rw [hγv, mul_assoc]
    have hd := hasDerivAt_blockFourierCoefficient_comp h hφ hα hγc hLu hγ' 0
    refine hd.congr_deriv ?_
    rw [hδ, hLpq]
    simp_rw [hLd]
    rw [sum_mul_diagVec, diagVec_ia, diagVec_ib, hq]
    simp only [Int.cast_zero, Complex.ofReal_zero, mul_zero, zero_div, sub_zero, add_zero,
      zero_add, sub_self, zero_mul]
    ring
  have := Langlands.Automorphic.OperatorRealization.eq_exp_mul_of_hasDerivAt hF 1
  simpa only [hγ, one_smul, zero_smul, matrixExpUnit_zero, one_mul, Complex.ofReal_one,
    mul_one] using this

/-- **Block invariance.** If `α_p - α_{p+1} = 2`, the rotation average `Φ^p_0 φ` is block
covariant with exponents `α_p - 1, α_p - 1`:
`Φ^p_0 φ (b(x, y, w) g) = e^{(α_p - 1)(x + y)} Φ^p_0 φ (g)`. -/
theorem isBlockCovariant_blockFourierCoefficient_zero (h : p + 1 < N)
    (hφ : ContMDiff (matrixModel ℝ N) 𝓘(ℝ, ℂ) ∞ φ) {α : Fin N → ℂ} (hα : IsExpEquivariant α φ)
    (hδ : α (ia h) - α (ib h) = 2) :
    IsBlockCovariant h (α (ia h) - 1) (α (ia h) - 1) (blockFourierCoefficient N p 0 φ) := by
  intro x y w g
  rw [blockB, mul_assoc, blockFourierCoefficient_zero_expDiag_mul h hφ hα hδ,
    blockFourierCoefficient_zero_upperUnit_mul h hφ hα hδ]
  congr 2
  ring

end Invariance

/-! ## Several disjoint blocks -/

/-- The factor `∏_i e^{(α_{p_i} - 1)(x_i + y_i)}`. -/
def detFactor (α : Fin N → ℂ) (slots : List (Slot N)) : ℂ :=
  (slots.map fun s => Complex.exp ((α (ia s.hp) - 1) * ((s.x : ℂ) + s.y))).prod

/-- **Block invariance for several blocks.** For pairwise disjoint blocks with
`α_{p_i} - α_{p_i + 1} = 2` and modes `j_i = 0`, the iterated rotation average satisfies
`Φ_0 ⋯ Φ_0 φ (b_1 ⋯ b_r g) = ∏_i e^{(α_{p_i} - 1)(x_i + y_i)} · Φ_0 ⋯ Φ_0 φ (g)`. -/
theorem coeffs_point_mul {φ : Langlands.GeneralLinear N ℝ → ℂ}
    (hφ : ContMDiff (matrixModel ℝ N) 𝓘(ℝ, ℂ) ∞ φ) {α : Fin N → ℂ} (hα : IsExpEquivariant α φ) :
    ∀ slots : List (Slot N), slots.Pairwise Slot.Disjoint → (∀ s ∈ slots, s.j = 0) →
      (∀ s ∈ slots, α (ia s.hp) - α (ib s.hp) = 2) →
      ∀ g : Langlands.GeneralLinear N ℝ,
        coeffs slots φ (point slots * g) = detFactor α slots * coeffs slots φ g
  | [], _, _, _, g => by simp [coeffs, point, detFactor]
  | s :: rest, hpw, hj, hδ, g => by
    obtain ⟨hsd, hrest⟩ := List.pairwise_cons.mp hpw
    have hsd' : ∀ t ∈ rest, s.p + 1 < t.p ∨ t.p + 1 < s.p := hsd
    have hs0 : s.j = 0 := hj s List.mem_cons_self
    have hc : Continuous φ := hφ.continuous
    have IH := coeffs_point_mul hφ hα rest hrest (fun t ht => hj t (List.mem_cons_of_mem _ ht))
      (fun t ht => hδ t (List.mem_cons_of_mem _ ht))
    have hcov : IsBlockCovariant s.hp (α (ia s.hp) - 1) (α (ia s.hp) - 1)
        (coeffs rest (blockFourierCoefficient N s.p 0 φ)) :=
      isBlockCovariant_coeffs s.hp
        (isBlockCovariant_blockFourierCoefficient_zero s.hp hφ hα (hδ s List.mem_cons_self))
        rest hsd'
    have hrot : blockFourierCoefficient N s.p 0 (coeffs rest φ) (point rest * g) =
        detFactor α rest * blockFourierCoefficient N s.p 0 (coeffs rest φ) g := by
      unfold blockFourierCoefficient
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun θ _ => ?_
      rw [← mul_assoc, blockRotation_mul_point s.hp θ rest hsd', mul_assoc, IH, mul_assoc]
    simp only [coeffs, point]
    rw [hs0, mul_assoc, blockFourierCoefficient_coeffs 0 hc rest hsd', hcov,
      ← blockFourierCoefficient_coeffs 0 hc rest hsd', hrot]
    have hdf : detFactor α (s :: rest) =
        Complex.exp ((α (ia s.hp) - 1) * ((s.x : ℂ) + s.y)) * detFactor α rest := by
      simp only [detFactor, List.map_cons, List.prod_cons]
    rw [hdf, show (α (ia s.hp) - 1) * (s.x : ℂ) + (α (ia s.hp) - 1) * (s.y : ℂ) =
      (α (ia s.hp) - 1) * ((s.x : ℂ) + s.y) by ring]
    ring

end RealInducedBlockInvariance

open RealInducedBlockBound RealInducedBlockInvariance RealBlockRotation in
/-- **Block invariance of iterated rotation averages.** For a smooth `φ` with
`IsExpEquivariant α φ` and pairwise disjoint slots of mode `0` at which
`α_{p} - α_{p + 1} = 2`, `coeffs slots φ (point slots * g) = detFactor α slots * coeffs slots φ g`. -/
def RealInducedBlockInvarianceStatement : Prop :=
  ∀ (N : ℕ) (φ : Langlands.GeneralLinear N ℝ → ℂ), ContMDiff (matrixModel ℝ N) 𝓘(ℝ, ℂ) ∞ φ →
    ∀ α : Fin N → ℂ, RealBlockDerivative.IsExpEquivariant α φ →
    ∀ slots : List (Slot N), slots.Pairwise Slot.Disjoint → (∀ s ∈ slots, s.j = 0) →
      (∀ s ∈ slots, α (ia s.hp) - α (ib s.hp) = 2) →
      ∀ g : Langlands.GeneralLinear N ℝ,
        coeffs slots φ (point slots * g) = detFactor α slots * coeffs slots φ g

theorem realInducedBlockInvariance : RealInducedBlockInvarianceStatement :=
  fun _ _ hφ _ hα slots hpw hj hδ g =>
    RealInducedBlockInvariance.coeffs_point_mul hφ hα slots hpw hj hδ g

end Langlands.Archimedean

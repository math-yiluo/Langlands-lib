import Langlands.Representation.Archimedean.RealBlockTestVector
import Langlands.Representation.Archimedean.RealStandardNontrivialProof
import Langlands.Representation.Archimedean.RealBlockNonvanishing
import Langlands.Representation.Archimedean.RealBlockJacquetFunctional
import Langlands.Representation.Archimedean.RealBlockLeftDerivative
import Langlands.Representation.Archimedean.RealBlockPositionData
import Langlands.Representation.Archimedean.RealCharacterPairData
import Langlands.Representation.Archimedean.RealSwapLandingAlgebra
import Langlands.Representation.Archimedean.RealGLTwoPrincipalSeriesUnitaryBoundStatement

noncomputable section

open scoped ComplexConjugate Manifold ContDiff TensorProduct Matrix Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean

namespace RealGLTwoPrincipalSeriesUnitaryBound

open RealBlockRotation RealBlockFourierFinite RealBlockTestVector RealBlockDerivative RealBlockJacquet
open TranslateFinite Langlands.GeneralLinear

private abbrev pair (c d : RealCharacterData) : List RealBlock := [.character c, .character d]

private abbrev G := Langlands.GeneralLinear 2 ℝ

private abbrev KFin (c d : RealCharacterData) :=
  kFiniteFunctions (realStandardModule 2 (pair c d)) (unitaryCompact ℝ 2)

private theorem adjacent : 0 + 1 < 2 := by decide

private abbrev rotation (θ : ℝ) : G := blockRotation 2 0 θ

-- An element of O(2) is a diagonal matrix times a rotation. Its second row determines
-- the angle, and the determinant gives the factor in the first row.
private theorem exists_diagonal_mul_rotation (g : G) (hg : g ∈ unitaryCompact ℝ 2) :
    ∃ (s : Fin 2 → ℝˣ) (θ : ℝ), g = Iwasawa.diagonalUnits s * rotation θ := by
  let A : Matrix (Fin 2) (Fin 2) ℝ := g
  have hA : A * Aᵀ = 1 := RealPrincipalSeriesDuality.mul_transpose_self_of_mem ⟨g, hg⟩
  have hrow := congrFun (congrFun hA 1) 1
  have hperp := congrFun (congrFun hA 0) 1
  norm_num [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two,
    Matrix.one_apply] at hrow hperp
  have hrow' : A 1 1 ^ 2 + A 1 0 ^ 2 = 1 := by nlinarith only [hrow]
  have hnz : A 1 1 ≠ 0 ∨ A 1 0 ≠ 0 := by
    by_contra! h
    simp [h.1, h.2] at hrow'
  obtain ⟨θ, r, hr, hs, hc, hsin⟩ := RealStandardNontrivial.exists_polar hnz
  have hr1 : r = 1 := by nlinarith only [hr, hs, hrow']
  simp only [hr1, mul_one] at hc hsin
  have h00 : A.det * A 1 1 = A 0 0 := by
    rw [Matrix.det_fin_two]
    linear_combination A 0 0 * hrow - A 1 0 * hperp
  have h01 : -(A.det * A 1 0) = A 0 1 := by
    rw [Matrix.det_fin_two]
    linear_combination A 0 1 * hrow - A 1 1 * hperp
  have hd : A.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det A).mp g.isUnit).ne_zero
  let s : Fin 2 → ℝˣ := ![Units.mk0 A.det hd, 1]
  refine ⟨s, θ, Units.ext ?_⟩
  ext i j
  change A i j = _
  rw [Units.val_mul, Iwasawa.diagonalUnits_val, Matrix.diagonal_mul, blockRotation_apply adjacent]
  fin_cases i <;> fin_cases j <;> norm_num [s, hc, hsin, h00, h01, mul_neg]

private theorem eq_of_rotation {c d : RealCharacterData} {f g : KFin c d}
    (h : ∀ θ, (f : G → ℂ) (rotation θ) = (g : G → ℂ) (rotation θ)) : f = g := by
  apply Subtype.ext
  apply eq_of_eqOn_unitaryCompact_of_mem_principalSeries f.2.1.1 g.2.1.1
  intro k hk
  obtain ⟨s, θ, rfl⟩ := exists_diagonal_mul_rotation k hk
  have hf := f.2.1.1.2 s 1 (rotation θ)
  have hg := g.2.1.1.2 s 1 (rotation θ)
  rw [OneMemClass.coe_one, mul_one] at hf hg
  rw [hf, hg, h]

private def IsMode {c d : RealCharacterData} (j : ℤ) (f : KFin c d) : Prop :=
  ∀ θ, (f : G → ℂ) (rotation θ) = expMode j θ

private def modePolynomial (p a b : ℕ) (A : Matrix (Fin 2) (Fin 2) ℝ) : ℂ :=
  (A.det : ℂ) ^ p * ((A 1 1 : ℂ) + (A 1 0 : ℂ) * Complex.I) ^ a *
    ((A 1 1 : ℂ) - (A 1 0 : ℂ) * Complex.I) ^ b

private theorem modePolynomial_sign (p a b : ℕ) :
    IsSignEq (![p, p + a + b] : Fin 2 → ℕ) (modePolynomial p a b) := by
  intro s _ A
  simp only [modePolynomial, Matrix.det_mul, Matrix.det_diagonal, Fin.prod_univ_two,
    Matrix.diagonal_mul, Complex.ofReal_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show (s 1 : ℂ) * A 1 1 + (s 1 : ℂ) * A 1 0 * Complex.I =
      s 1 * (A 1 1 + (A 1 0 : ℂ) * Complex.I) by ring,
    show (s 1 : ℂ) * A 1 1 - (s 1 : ℂ) * A 1 0 * Complex.I =
      s 1 * (A 1 1 - (A 1 0 : ℂ) * Complex.I) by ring]
  simp only [mul_pow, pow_add]
  ring

private theorem exists_mode (c d : RealCharacterData) (j : ℤ)
    (hj : (j - c.parity.val - d.parity.val) % 2 = 0) : ∃ f : KFin c d, IsMode j f := by
  let a := j.toNat
  let b := (-j).toNat
  have hab : (a : ℤ) - b = j := by dsimp [a, b]; omega
  have hpar : (c.parity.val + a + b) % 2 = d.parity.val := by
    have hd := d.parity.isLt
    omega
  have hdet := RealBlockNonvanishing.isTranslateFinite_det
    (M := fun κ : Matrix.unitaryGroup (Fin 2) ℝ => (κ : Matrix (Fin 2) (Fin 2) ℝ))
    (fun i k => isTranslateFinite_entry (i, k))
  have hplus := isTranslateFinite_add (isTranslateFinite_entry ((1 : Fin 2), (1 : Fin 2)))
    (isTranslateFinite_smul (isTranslateFinite_entry ((1 : Fin 2), (0 : Fin 2))) Complex.I)
  have hminus := isTranslateFinite_add (isTranslateFinite_entry ((1 : Fin 2), (1 : Fin 2)))
    (isTranslateFinite_smul (isTranslateFinite_entry ((1 : Fin 2), (0 : Fin 2))) (-Complex.I))
  have hfinite : IsTranslateFinite (id : Matrix.unitaryGroup (Fin 2) ℝ → _)
      (fun κ => modePolynomial c.parity.val a b κ) := by
    simpa only [modePolynomial, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_comm Complex.I,
      neg_mul, sub_eq_add_neg] using
      isTranslateFinite_mul (isTranslateFinite_mul (isTranslateFinite_pow hdet c.parity.val)
        (isTranslateFinite_pow hplus a)) (isTranslateFinite_pow hminus b)
  have hcont : Continuous (modePolynomial c.parity.val a b) :=
    ((Complex.continuous_ofReal.comp continuous_id.matrix_det).pow _).mul
      (((continuous_entry (1 : Fin 2) 1).add
        ((continuous_entry (1 : Fin 2) 0).mul continuous_const)).pow _)
      |>.mul (((continuous_entry (1 : Fin 2) 1).sub
        ((continuous_entry (1 : Fin 2) 0).mul continuous_const)).pow _)
  obtain ⟨f, hf⟩ := exists_KF (ds := pair c d) (by rfl) hcont hfinite
    (modePolynomial_sign c.parity.val a b) (by
      intro i
      fin_cases i
      · simpa [realPositionCharacter] using (RealCharacterPair.character_neg_one c).symm
      · change (-1 : ℂ) ^ (c.parity.val + a + b) = d.character (-1)
        rw [RealCharacterPair.character_neg_one, neg_one_pow_eq_pow_mod_two, hpar]) (by
      intro p z hz
      cases p with
      | zero => simp [realInducedBlockAt] at hz
      | succ p => cases p <;> simp [realInducedBlockAt] at hz)
  refine ⟨f, fun θ => ?_⟩
  rw [hf _ (blockRotation_mem_unitaryCompact 2 0 θ)]
  have hd : (rotation θ : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    simp only [Matrix.det_fin_two, blockRotation_apply adjacent]
    norm_num
    nlinarith only [Real.sin_sq_add_cos_sq θ]
  simp only [modePolynomial, hd, Complex.ofReal_one, one_pow, one_mul,
    blockRotation_apply adjacent]
  norm_num
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [show (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I = expMode 1 θ by
      rw [expMode_one_eq, mul_comm Complex.I],
    show (Real.cos θ : ℂ) - (Real.sin θ : ℂ) * Complex.I = expMode (-1) θ by
      rw [expMode_neg_one_eq, mul_comm Complex.I]]
  rw [expMode, expMode, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add, expMode]
  congr 1
  have hab' : (a : ℂ) - b = j := by exact_mod_cast hab
  linear_combination ((θ : ℂ) * Complex.I) * hab'

private def H : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![1, -1]

private abbrev actH {c d : RealCharacterData} (f : KFin c d) : KFin c d :=
  realStandardLie 2 (pair c d) (1 ⊗ₜ H) f

private abbrev ν (c d : RealCharacterData) : ℂ := c.exponent - d.exponent

private theorem coeff_actH {c d : RealCharacterData} (f : KFin c d) (k : ℤ) :
    blockFourierCoefficient 2 0 k (actH f) 1 =
      (ν c d + 1 + k - 2) / 2 * blockFourierCoefficient 2 0 (k - 2) f 1 +
      (ν c d + 1 - k - 2) / 2 * blockFourierCoefficient 2 0 (k + 2) f 1 := by
  have hτ := isExpEquivariant_of_mem_principalSeries
    (fun (i : Fin 2) x => RealBlockPosition.realPositionCharacter_exp (pair c d) i x)
    f.2.1.1
  have hH : H.IsUpperTriangular := by
    intro i j hij
    change j < i at hij
    simp [H, ne_of_gt hij]
  have hF := blockFourierCoefficient_rightDerivative adjacent
    (contMDiff_of_mem_realStandardModule f.2.1) hτ hH (X := H) 1 (by simp) k
  rw [realStandardLie_one_tmul_apply_coe]
  norm_num [H, ia, ib, Fin.sum_univ_two, GramFormula.realPositionExponent] at hF
  unfold H
  linear_combination hF

private theorem coeff_mode {c d : RealCharacterData} {f : KFin c d} {j : ℤ}
    (hf : IsMode j f) (k : ℤ) :
    blockFourierCoefficient 2 0 k f 1 = if j = k then 2 * (Real.pi : ℂ) else 0 := by
  rw [blockFourierCoefficient_eq_coeff, show (fun θ => (f : G → ℂ) (rotation θ * 1)) =
    expMode j by funext θ; rw [mul_one, hf θ], coeff_expMode]

private theorem actH_mode {c d : RealCharacterData} {f fPlus fMinus : KFin c d} {j : ℤ}
    (hf : IsMode j f) (hPlus : IsMode (j + 2) fPlus) (hMinus : IsMode (j - 2) fMinus) :
    actH f = ((ν c d + 1 + j) / 2) • fPlus + ((ν c d + 1 - j) / 2) • fMinus := by
  apply eq_of_rotation
  intro θ
  refine RealSwapLandingAlgebra.eq_of_blockFourierCoefficient_eq adjacent
    (continuous_coe _) (continuous_coe _) (rotation θ) fun k => ?_
  rw [← mul_one (rotation θ), blockFourierCoefficient_blockRotation_mul adjacent,
    blockFourierCoefficient_blockRotation_mul adjacent]
  congr 1
  rw [coeff_actH, Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul,
    blockFourierCoefficient_add 0 k ((continuous_coe fPlus).const_smul _)
      ((continuous_coe fMinus).const_smul _),
    blockFourierCoefficient_smul, blockFourierCoefficient_smul,
    coeff_mode hf, coeff_mode hf, coeff_mode hPlus, coeff_mode hMinus]
  simp only [show j = k - 2 ↔ j + 2 = k by omega, show j = k + 2 ↔ j - 2 = k by omega]
  split_ifs <;> try omega
  all_goals simp only [mul_zero, zero_add, add_zero]
  all_goals (subst k; push_cast; ring)

private def compactRotation (θ : ℝ) : Matrix.unitaryGroup (Fin 2) ℝ :=
  ⟨(rotation θ : Matrix (Fin 2) (Fin 2) ℝ), blockRotation_mem_unitaryCompact 2 0 θ⟩

private theorem rotation_on_mode {c d : RealCharacterData} {f : KFin c d} {j : ℤ}
    (hf : IsMode j f) (θ : ℝ) :
    realStandardRep 2 (pair c d) (compactRotation θ) f = expMode j θ • f := by
  have hθ : Unitary.toUnits (compactRotation θ) = rotation θ := Units.ext rfl
  apply eq_of_rotation
  intro φ
  rw [realStandardRep_apply_coe, hθ]
  change (f : G → ℂ) (rotation φ * rotation θ) = expMode j θ * (f : G → ℂ) (rotation φ)
  rw [← blockRotation_add, hf, hf, expMode, expMode, expMode, Complex.ofReal_add, ← Complex.exp_add]
  congr 1
  ring

private theorem conj_mul_expMode (j : ℤ) (θ : ℝ) :
    conj (expMode j θ) * expMode j θ = 1 := by
  simp only [expMode, ← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal,
    map_intCast, mul_neg, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero]

private theorem inner_smul_right {c d : RealCharacterData}
    (b : Langlands.InvariantPositiveForm (realStandardRep 2 (pair c d)))
    (f g : KFin c d) (z : ℂ) : b.inner f (z • g) = z * b.inner f g := by
  let : InnerProductSpace.Core ℂ (KFin c d) := b.toInnerProductCore
  exact InnerProductSpace.Core.inner_smul_right (𝕜 := ℂ) f g (r := z)

private theorem orthogonal_modes {c d : RealCharacterData}
    (b : Langlands.InvariantPositiveForm (realStandardRep 2 (pair c d)))
    {f g : KFin c d} {j k : ℤ} (hf : IsMode j f) (hg : IsMode k g) (hk : j + 4 = k) :
    b.inner f g = 0 := by
  subst k
  have hfour : expMode 4 (Real.pi / 4) = -1 := by
    rw [expMode, Complex.ofReal_div]
    convert Complex.exp_pi_mul_I using 2
    push_cast
    ring
  have hphase : expMode (j + 4) (Real.pi / 4) = -expMode j (Real.pi / 4) := by
    rw [← congr_fun (expMode_add j 4) (Real.pi / 4), Pi.mul_apply, hfour, mul_neg_one]
  have hb := b.invariant (compactRotation (Real.pi / 4)) f g
  rw [rotation_on_mode hf, rotation_on_mode hg, b.smul_left, inner_smul_right b, hphase,
    ← mul_assoc, mul_neg, conj_mul_expMode,
    neg_mul, one_mul] at hb
  exact CharZero.neg_eq_self_iff.mp hb

private theorem mode_inner_pos {c d : RealCharacterData}
    (b : Langlands.InvariantPositiveForm (realStandardRep 2 (pair c d)))
    {f : KFin c d} {j : ℤ} (hf : IsMode j f) :
    0 < (b.inner f f).re := by
  let : InnerProductSpace.Core ℂ (KFin c d) := b.toInnerProductCore
  refine lt_of_le_of_ne (b.re_inner_nonneg f) fun hz => ?_
  have hzero : f = 0 := (InnerProductSpace.Core.normSq_eq_zero (𝕜 := ℂ)).mp hz.symm
  have hval := hf 0
  simp [hzero, expMode] at hval

private theorem adjacent_mode_relation {c d : RealCharacterData}
    (b : Langlands.InvariantPositiveForm (realStandardRep 2 (pair c d)))
    (hskew : ∀ f g : KFin c d, b.inner (actH f) g + b.inner f (actH g) = 0)
    (j : ℤ) (hj : (j - c.parity.val - d.parity.val) % 2 = 0) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧
      ((ν c d).re + 1 + j) * B + ((ν c d).re - 1 - j) * A = 0 := by
  let : InnerProductSpace.Core ℂ (KFin c d) := b.toInnerProductCore
  obtain ⟨f, hf⟩ := exists_mode c d j hj
  obtain ⟨fPlus, hPlus⟩ := exists_mode c d (j + 2) (by omega)
  obtain ⟨fMinus, hMinus⟩ := exists_mode c d (j - 2) (by omega)
  obtain ⟨g, hg⟩ := exists_mode c d (j + 2 + 2) (by omega)
  have hsk := hskew f fPlus
  have h1 := orthogonal_modes b hMinus hPlus (by omega)
  have h2 := orthogonal_modes b hf hg (by omega)
  rw [actH_mode hf hPlus hMinus,
    actH_mode hPlus hg (by simpa only [add_sub_cancel_right] using hf)] at hsk
  simp only [b.add_left, InnerProductSpace.Core.inner_add_right (𝕜 := ℂ), b.smul_left,
    inner_smul_right b, h1, h2, mul_zero, add_zero, zero_add] at hsk
  refine ⟨(b.inner f f).re, (b.inner fPlus fPlus).re, mode_inner_pos b hf,
    mode_inner_pos b hPlus, ?_⟩
  have hfim : (b.inner f f).im = 0 := InnerProductSpace.Core.inner_self_im (𝕜 := ℂ) f
  have hpim : (b.inner fPlus fPlus).im = 0 := InnerProductSpace.Core.inner_self_im (𝕜 := ℂ) fPlus
  have hden (z : ℂ) : (z / 2).re = z.re / 2 := by
    exact RCLike.div_re_ofReal (K := ℂ) (z := z) (r := 2)
  have hre := congrArg Complex.re hsk
  simp only [Complex.add_re, Complex.zero_re, Complex.mul_re, Complex.conj_re,
    hfim, hpim, mul_zero, sub_zero, hden, Complex.sub_re, Complex.one_re,
    Complex.intCast_re] at hre
  push_cast at hre
  simp only [ν, Complex.sub_re]
  linear_combination 2 * hre

/-- Infinitesimal unitarity of a real principal series of two characters forces a
strict bound on the real difference of their exponents. For opposite parities that
difference is zero. -/
theorem exponent_difference : RealGLTwoPrincipalSeriesUnitaryBoundStatement := by
  intro c d hu
  obtain ⟨b, hb⟩ := hu
  by_cases hParity : c.parity = d.parity
  · have hj : ((0 : ℤ) - c.parity.val - d.parity.val) % 2 = 0 := by rw [hParity]; omega
    obtain ⟨A, B, hA, hB, heq⟩ := adjacent_mode_relation b (hb H) 0 hj
    simp only [Int.cast_zero, add_zero, sub_zero] at heq
    refine ⟨abs_lt.mpr ⟨?_, ?_⟩, fun h => (h hParity).elim⟩
    · by_contra! hx
      have h₁ := mul_nonpos_of_nonpos_of_nonneg
        (show (ν c d).re + 1 ≤ 0 by linarith) hB.le
      have h₂ := mul_neg_of_neg_of_pos (show (ν c d).re - 1 < 0 by linarith) hA
      linarith
    · by_contra! hx
      have h₁ := mul_pos (show 0 < (ν c d).re + 1 by linarith) hB
      have h₂ := mul_nonneg (show 0 ≤ (ν c d).re - 1 by linarith) hA.le
      linarith
  · have hc := c.parity.isLt
    have hd := d.parity.isLt
    have hval : c.parity.val ≠ d.parity.val := fun h => hParity (Fin.ext h)
    have hj : ((-1 : ℤ) - c.parity.val - d.parity.val) % 2 = 0 := by omega
    obtain ⟨A, B, hA, hB, heq⟩ := adjacent_mode_relation b (hb H) (-1) hj
    push_cast at heq
    have hprod : (ν c d).re * (A + B) = 0 := by linear_combination heq
    have hz := (mul_eq_zero.mp hprod).resolve_right (add_pos hA hB).ne'
    refine ⟨?_, fun _ => hz⟩
    change |(ν c d).re| < 1
    norm_num [hz]

end RealGLTwoPrincipalSeriesUnitaryBound

end Langlands.Archimedean

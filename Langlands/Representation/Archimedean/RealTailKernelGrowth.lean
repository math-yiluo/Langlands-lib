import Langlands.Representation.Archimedean.RealInducedCharacterMaps
import Langlands.Representation.Archimedean.RealTaylorLeftPolynomialProof
import Langlands.Representation.Archimedean.RealLeftPolynomialGrowthProof
import Langlands.Representation.Archimedean.RealPrincipalSeriesDualityProof
import Langlands.Representation.Archimedean.RealBlockPositionData
import Mathlib.Analysis.Calculus.ContDiff.Polynomial

/-! # The kernel of the ascending tail map grows slowly -/

noncomputable section

open scoped Manifold ContDiff Matrix.Norms.Operator Topology Nat TensorProduct

open Filter Asymptotics Polynomial

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

namespace RealTailKernel

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open RealBlockRotation RealBlockDerivative RealTaylorLeftPolynomialProof

/-! ## An Iwasawa decomposition of the lower root element -/

section Iwasawa

variable {n p : ℕ} (hp : p + 1 < n)

/-- The diagonal exponents `-log √(1 + t²)` at `p` and `log √(1 + t²)` at `p + 1`. -/
def iwasawaExponent (t : ℝ) (i : Fin n) : ℝ :=
  if (i : ℕ) = p then -Real.log (Real.sqrt (1 + t ^ 2))
  else if (i : ℕ) = p + 1 then Real.log (Real.sqrt (1 + t ^ 2)) else 0

private theorem sqrt_pos' (t : ℝ) : 0 < Real.sqrt (1 + t ^ 2) :=
  Real.sqrt_pos.mpr (by positivity)

private theorem sqrt_sq' (t : ℝ) : Real.sqrt (1 + t ^ 2) ^ 2 = 1 + t ^ 2 :=
  Real.sq_sqrt (by positivity)

/-- `e(t) = exp(diag x) · (1 + t E_{p,p+1}) · r_p(arctan t)`, where `x` has entries
`-log √(1 + t²)` at `p` and `log √(1 + t²)` at `p + 1`. -/
theorem lowerRootElement_eq_iwasawa (t : ℝ) :
    lowerRootElement n p hp t =
      matrixExpUnit n (Matrix.diagonal (iwasawaExponent (n := n) (p := p) t)) *
        upperRootElement hp t * blockRotation n p (Real.arctan t) := by
  set S := Real.sqrt (1 + t ^ 2) with hSdef
  have hS : 0 < S := sqrt_pos' t
  have hS2 : S ^ 2 = 1 + t ^ 2 := sqrt_sq' t
  rw [RealPrincipalSeriesDuality.matrixExpUnit_diagonal]
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Iwasawa.diagonalUnits_val]
  ext i k
  rw [mul_blockRotation_apply hp, Real.cos_arctan, Real.sin_arctan, ← hSdef]
  have hexp1 : Real.exp (-Real.log S) = S⁻¹ := by rw [Real.exp_neg, Real.exp_log hS]
  have hexp2 : Real.exp (Real.log S) = S := Real.exp_log hS
  have hSne : S ≠ 0 := hS.ne'
  simp only [lowerRootElement_val, upperRootElement_val, upperRootMatrix, lowerRootMatrix,
    Matrix.diagonal_mul, Matrix.add_apply, Matrix.smul_apply, Matrix.single_apply,
    Matrix.one_apply, smul_eq_mul, iwasawaExponent, ia, ib, idxP, idxQ, Fin.ext_iff,
    Units.val_mk0]
  simp only [← hSdef]
  have hpq : p + 1 ≠ p := Nat.succ_ne_self p
  have hqp : p ≠ p + 1 := fun h => hpq h.symm
  rcases (by omega : (i : ℕ) = p ∨ (i : ℕ) = p + 1 ∨ ((i : ℕ) ≠ p ∧ (i : ℕ) ≠ p + 1)) with
    hi | hi | ⟨hi1, hi2⟩ <;>
  rcases (by omega : (k : ℕ) = p ∨ (k : ℕ) = p + 1 ∨ ((k : ℕ) ≠ p ∧ (k : ℕ) ≠ p + 1)) with
    hk | hk | ⟨hk1, hk2⟩
  · simp only [hi, hk, hpq, hqp, hexp1, ↓reduceIte, and_true, and_false]
    field_simp
    nlinarith [hS2]
  · simp only [hi, hk, hpq, hqp, hexp1, ↓reduceIte, and_true, and_false]
    field_simp
    ring
  · simp only [hi, hpq, hexp1, ↓reduceIte, and_false, hk1, hk2, Ne.symm hk1, Ne.symm hk2]
    ring
  · simp only [hi, hk, hpq, hqp, hexp2, ↓reduceIte, and_true, and_false]
    field_simp
    ring
  · simp only [hi, hk, hpq, hqp, hexp2, ↓reduceIte, and_true, and_false]
    field_simp
    ring
  · simp only [hi, hpq, hqp, hexp2, ↓reduceIte, and_false, hk1, hk2, Ne.symm hk1,
      Ne.symm hk2]
    ring
  · simp only [hk, hpq, ↓reduceIte, and_true, and_false, hi1, hi2, Ne.symm hi1,
      Ne.symm hi2, Real.exp_zero]
    ring
  · simp only [hk, hpq, hqp, ↓reduceIte, and_true, and_false, hi1, hi2, Ne.symm hi1,
      Ne.symm hi2, Real.exp_zero]
    ring
  · simp only [↓reduceIte, and_false, hi1, hi2, Ne.symm hi1, Ne.symm hi2, hk1, hk2,
      Ne.symm hk1, Ne.symm hk2, Real.exp_zero]
    ring

end Iwasawa

/-! ## The left exponential factor -/

section Factor

variable {n p : ℕ} (hp : p + 1 < n)

/-- For a function `F` with exponential left equivariance, `F(e(t) g)` is an exponential factor
times `F(r_p(arctan t) g)`. -/
theorem orbit_eq_of_isExpEquivariant {α : Fin n → ℂ} {F : Langlands.GeneralLinear n ℝ → ℂ}
    (hF : IsExpEquivariant α F) (t : ℝ) (g : Langlands.GeneralLinear n ℝ) :
    F (lowerRootElement n p hp t * g) =
      Complex.exp ((α (ib hp) - α (ia hp)) * ((Real.log (Real.sqrt (1 + t ^ 2)) : ℝ) : ℂ)) *
        F (blockRotation n p (Real.arctan t) * g) := by
  rw [lowerRootElement_eq_iwasawa hp t, mul_assoc _ (blockRotation n p (Real.arctan t)) g]
  rw [hF (iwasawaExponent t) ⟨upperRootElement hp t, upperRootElement_mem hp t⟩
    (blockRotation n p (Real.arctan t) * g)]
  congr 2
  rw [Fintype.sum_eq_add (ia hp) (ib hp) (ia_ne_ib hp)]
  · simp only [iwasawaExponent, ia, ib, ↓reduceIte, Nat.succ_ne_self]
    push_cast
    ring
  · intro i hi
    have h1 : (i : ℕ) ≠ p := fun h => hi.1 (Fin.ext h)
    have h2 : (i : ℕ) ≠ p + 1 := fun h => hi.2 (Fin.ext h)
    simp [iwasawaExponent, h1, h2]

end Factor

/-! ## Modes of degree at most `ℓ - 1` -/

section Modes

/-- The polynomial `(1 + i X)^m (1 - i X)^m'`. -/
def modePoly (m m' : ℕ) : Polynomial ℂ :=
  (1 + Polynomial.C Complex.I * Polynomial.X) ^ m * (1 - Polynomial.C Complex.I * Polynomial.X) ^ m'

theorem modePoly_natDegree_le (m m' : ℕ) : (modePoly m m').natDegree ≤ m + m' := by
  have h1 : (1 + Polynomial.C Complex.I * Polynomial.X).natDegree ≤ 1 := by compute_degree
  have h2 : (1 - Polynomial.C Complex.I * Polynomial.X).natDegree ≤ 1 := by compute_degree
  unfold modePoly
  refine (natDegree_mul_le).trans (add_le_add ?_ ?_)
  · exact (natDegree_pow_le).trans (by nlinarith)
  · exact (natDegree_pow_le).trans (by nlinarith)

/-- `√(1 + t²)^(m + m') e^{i (m - m') arctan t} = (1 + i t)^m (1 - i t)^m'`. -/
theorem sqrt_pow_mul_expMode (m m' : ℕ) (t : ℝ) :
    ((Real.sqrt (1 + t ^ 2) : ℝ) : ℂ) ^ (m + m') *
        RealBlockFourierFinite.expMode ((m : ℤ) - m') (Real.arctan t) =
      (modePoly m m').eval (t : ℂ) := by
  set S : ℝ := Real.sqrt (1 + t ^ 2) with hSdef
  have hS : 0 < S := sqrt_pos' t
  have hS2 : S ^ 2 = 1 + t ^ 2 := sqrt_sq' t
  have hSC : (S : ℂ) ≠ 0 := by exact_mod_cast hS.ne'
  set θ : ℝ := Real.arctan t with hθ
  have hc : Real.cos θ = 1 / S := by rw [hθ, Real.cos_arctan]
  have hs : Real.sin θ = t / S := by rw [hθ, Real.sin_arctan]
  have he1 : Complex.exp ((θ : ℂ) * Complex.I) = ((1 + Complex.I * t) / S : ℂ) := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, hc, hs]
    push_cast
    field_simp
  have he2 : Complex.exp (-((θ : ℂ) * Complex.I)) = ((1 - Complex.I * t) / S : ℂ) := by
    rw [← neg_mul, ← Complex.ofReal_neg, Complex.exp_mul_I, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg, hc, hs]
    push_cast
    field_simp
    ring
  have hmode : RealBlockFourierFinite.expMode ((m : ℤ) - m') θ =
      Complex.exp ((θ : ℂ) * Complex.I) ^ m * Complex.exp (-((θ : ℂ) * Complex.I)) ^ m' := by
    rw [RealBlockFourierFinite.expMode, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul,
      ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hmode, he1, he2, pow_add, div_pow, div_pow]
  simp only [modePoly, eval_mul, eval_pow, eval_add, eval_sub, eval_one, eval_C, eval_X]
  field_simp

end Modes

/-- A complex polynomial of degree `< k`, as a function of a real variable, has vanishing
`k`-th derivative at `0`. -/
theorem iteratedDeriv_eval_eq_zero {Q : Polynomial ℂ} {k : ℕ} (hQ : Q.natDegree < k) :
    iteratedDeriv k (fun t : ℝ => Q.eval (t : ℂ)) 0 = 0 := by
  have hf : ContDiffOn ℝ k (fun t : ℝ => Q.eval (t : ℂ)) Set.univ := by
    have h := ((Q.contDiff_aeval (𝕜 := ℂ) k).restrict_scalars ℝ).comp
      (Complex.ofRealCLM.contDiff (n := k))
    have heq : (fun t : ℝ => Q.eval (t : ℂ)) =
        (fun x : ℂ => Polynomial.aeval x Q) ∘ Complex.ofRealCLM := by
      funext t
      simp [Polynomial.coe_aeval_eq_eval]
    rw [heq]
    exact h.contDiffOn
  have h := iteratedDeriv_eq_of_isLittleO isOpen_univ convex_univ (Set.mem_univ 0) hf hQ.le
    (by simpa only [sub_self] using Asymptotics.isLittleO_zero (fun t : ℝ => t ^ k) (𝓝 0))
  rw [h, Polynomial.coeff_eq_zero_of_natDegree_lt hQ, mul_zero]

/-! ## The kernel of the ascending tail map -/

section Tail

open RealInducedCharacter RealBlockFrobeniusMap RealCharacterPair RealCharacterPairReducible
  RealBlockMultiplier RealBlockJacquet RealBlockFourierFinite RealBlockPosition

variable {n : ℕ} {pre post : List RealBlock} {d : ComplexCharacterData} {sa sb : Fin 2}

/-- The ascending list `pre ++ [c_b, c_a] ++ post` of the tail map. -/
abbrev tailList (pre post : List RealBlock) (d : ComplexCharacterData) (sa sb : Fin 2) :
    List RealBlock :=
  pre ++ [RealBlock.character (cb d sb), RealBlock.character (ca d sa)] ++ post

theorem exponent_tailList_zero :
    GramFormula.realPositionExponent (tailList pre post d sa sb) (realRank pre) = bExp d :=
  exponent_mid_zero pre post (by rw [realRank_tail_pair]; norm_num)

theorem exponent_tailList_one :
    GramFormula.realPositionExponent (tailList pre post d sa sb) (realRank pre + 1) = aExp d :=
  exponent_mid_one pre post (by rw [realRank_tail_pair]; norm_num)

variable (hn : realRank (pre ++ [RealBlock.induced d] ++ post) = n) (hl : 0 < d.weight.natAbs)
  (hs : (sa.val + sb.val) % 2 = (d.weight.natAbs + 1) % 2)

/-- The block Fourier modes on `O(n)` of a vector in the kernel of the tail map lie in the
parity class and have weight `|j| < ℓ`. -/
theorem kernel_fourier_support (h : RealStandardFiltration.KF n (tailList pre post d sa sb))
    (hh : blockFrobMap (data_tail hn hl hs) h = 0) {κ : Langlands.GeneralLinear n ℝ}
    (hκ : κ ∈ unitaryCompact ℝ n) (j : ℤ)
    (hj : blockFourierCoefficient n (realRank pre) j h κ ≠ 0) :
    Even (j - pairParity (cb d sb) (ca d sa)) ∧ |j| < d.weight.natAbs := by
  have hdata := data_tail hn hl hs
  have hpar := tail_parity (d := d) hs
  have hε := pairParity_eq (cb d sb) (ca d sa)
  by_cases hev : Even (j - pairParity (cb d sb) (ca d sa))
  · refine ⟨hev, ?_⟩
    by_contra hlt
    have hlt := not_lt.mp hlt
    have hlt' : (d.weight.natAbs : ℤ) < |j| := by
      rcases lt_or_eq_of_le hlt with h' | h'
      · exact h'
      · exact absurd (abs_lt_of_parity hpar hev (le_of_eq h'.symm)) (by omega)
    have hμ := (tailMultiplier_ne_zero_iff hl hε hpar (neg_one_pow_sq_fin sa) hev).mpr hlt'
    have hcoef := blockFourierCoefficient_blockFrobMap hdata h hκ j
    rw [hh, ZeroMemClass.coe_zero, blockFourierCoefficient_zero] at hcoef
    exact hj ((mul_eq_zero.mp hcoef.symm).resolve_left hμ)
  · exact absurd (blockFourierCoefficient_eq_zero_of_not_even hdata.lt hdata.par h hev κ) hj

/-- Along the lower root group of the block, a vector in the kernel of the tail map is a
polynomial of degree `< ℓ` at every point of `O(n)`. -/
theorem exists_poly_orbit (h : RealStandardFiltration.KF n (tailList pre post d sa sb))
    (hh : blockFrobMap (data_tail hn hl hs) h = 0) {κ : Langlands.GeneralLinear n ℝ}
    (hκ : κ ∈ unitaryCompact ℝ n) :
    ∃ Q : Polynomial ℂ, Q.natDegree < d.weight.natAbs ∧ ∀ t : ℝ,
      (h : Langlands.GeneralLinear n ℝ → ℂ)
          (lowerRootElement n (realRank pre) (data_tail hn hl hs).lt t * κ) =
        Q.eval (t : ℂ) := by
  classical
  have hp := (data_tail hn hl hs).lt
  set ℓ := d.weight.natAbs with hℓ
  set ε := pairParity (cb d sb) (ca d sa) with hεdef
  have hpar : Even ((ℓ : ℤ) - 1 - ε) := tail_parity (d := d) hs
  have hτ : ∀ (i : Fin n) (x : ℝ), realPositionCharacter (tailList pre post d sa sb) i
      (Units.mk0 (Real.exp x) (Real.exp_pos x).ne') =
        Complex.exp (GramFormula.realPositionExponent (tailList pre post d sa sb) i * x) :=
    fun i x => realPositionCharacter_exp _ i x
  have hexp := isExpEquivariant_of_mem_principalSeries hτ h.2.1.1
  have hdiff : ((GramFormula.realPositionExponent (tailList pre post d sa sb) (ib hp) +
        ((n : ℂ) - 1) / 2 - ((ib hp : ℕ) : ℂ)) -
      (GramFormula.realPositionExponent (tailList pre post d sa sb) (ia hp) +
        ((n : ℂ) - 1) / 2 - ((ia hp : ℕ) : ℂ))) = ((ℓ - 1 : ℕ) : ℂ) := by
    have h1 : ((ib hp : Fin n) : ℕ) = realRank pre + 1 := rfl
    have h0 : ((ia hp : Fin n) : ℕ) = realRank pre := rfl
    rw [h1, h0, exponent_tailList_one, exponent_tailList_zero, Nat.cast_sub hl,
      Nat.cast_one]
    have := aExp_sub_bExp d
    push_cast
    linear_combination this
  obtain ⟨D, -, hsum⟩ := exists_eq_sum_blockFourierCoefficient hp h.2.1.1.1.continuous h.2.2
  let good : ℤ → Prop := fun j => Even (j - ε) ∧ |j| < ℓ
  let mm : ℤ → ℕ := fun j => (((ℓ : ℤ) - 1 + j) / 2).toNat
  let mm' : ℤ → ℕ := fun j => (((ℓ : ℤ) - 1 - j) / 2).toNat
  have hgood : ∀ j, good j → ((mm j : ℤ) - mm' j = j ∧ mm j + mm' j = ℓ - 1) := by
    intro j ⟨hev, hlt⟩
    obtain ⟨r, hr⟩ := hpar
    obtain ⟨q, hq⟩ := hev
    have habs := abs_lt.mp hlt
    simp only [mm, mm']
    omega
  let Q : Polynomial ℂ := ∑ j ∈ Finset.Icc (-(D : ℤ)) D,
    Polynomial.C ((2 * (Real.pi : ℂ))⁻¹ * blockFourierCoefficient n (realRank pre) j h κ) *
      (if good j then modePoly (mm j) (mm' j) else 0)
  refine ⟨Q, ?_, fun t => ?_⟩
  · have hle : Q.natDegree ≤ ℓ - 1 := by
      refine natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
      refine (natDegree_C_mul_le _ _).trans ?_
      split_ifs with hj
      · exact (modePoly_natDegree_le _ _).trans (hgood j hj).2.le
      · simp
    omega
  · rw [orbit_eq_of_isExpEquivariant hp hexp t κ, hdiff, hsum κ hκ (Real.arctan t)]
    have hS : 0 < Real.sqrt (1 + t ^ 2) := sqrt_pos' t
    have hfac : Complex.exp (((ℓ - 1 : ℕ) : ℂ) * ((Real.log (Real.sqrt (1 + t ^ 2)) : ℝ) : ℂ)) =
        ((Real.sqrt (1 + t ^ 2) : ℝ) : ℂ) ^ (ℓ - 1) := by
      rw [Complex.exp_nat_mul, ← Complex.ofReal_exp, Real.exp_log hS]
    rw [hfac]
    simp only [Q, eval_finsetSum, eval_mul, eval_C, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hz : blockFourierCoefficient n (realRank pre) j h κ = 0
    · simp [hz]
    · have hj : good j := kernel_fourier_support hn hl hs h hh hκ j hz
      simp only [hj, ↓reduceIte]
      obtain ⟨hj1, hj2⟩ := hgood j hj
      rw [← sqrt_pow_mul_expMode, hj1, ← hj2]
      ring

/-- At the tail block the position characters satisfy `χ_{p+1}(x) = x^ℓ χ_p(x)` for
`x > 0`. -/
theorem tailList_character_relation (x : ℝˣ) (hx : 0 < (x : ℝ)) :
    realPositionCharacter (tailList pre post d sa sb) (realRank pre + 1) x =
      ((x : ℝ) : ℂ) ^ d.weight.natAbs *
        realPositionCharacter (tailList pre post d sa sb) (realRank pre) x := by
  have hxe : x = Units.mk0 (Real.exp (Real.log x)) (Real.exp_pos _).ne' :=
    Units.ext (by simp [Real.exp_log hx])
  rw [hxe, realPositionCharacter_exp, realPositionCharacter_exp, exponent_tailList_one,
    exponent_tailList_zero, Units.val_mk0, Complex.ofReal_exp, ← Complex.exp_nat_mul,
    ← Complex.exp_add]
  congr 1
  have := aExp_sub_bExp d
  linear_combination ((Real.log (x : ℝ) : ℝ) : ℂ) * this

open Langlands.Algebra.UniversalEnveloping in
/-- **Slow growth of the tail kernel.** The operators of degree `≤ k` of `U(ℂ ⊗_ℝ 𝔤𝔩_n(ℝ))`,
restricted to the kernel of the tail map, span a space of dimension at most
`C (k + 1)^(n (n - 1) - 1)`. -/
theorem tailKernel_growth :
    ∃ C : ℝ, ∀ k : ℕ,
      (Module.finrank ℂ ((degreeFiltration ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) k).map
        (LinearMap.lcomp ℂ _ (LinearMap.ker (blockFrobMap (data_tail hn hl hs))).subtype ∘ₗ
          (envelopingAction (realStandardLie n (tailList pre post d sa sb))).toLinearMap)) :
            ℝ) ≤
        C * ((k : ℝ) + 1) ^ (n * (n - 1) - 1) := by
  have hp := (data_tail hn hl hs).lt
  refine realLeftPolynomialGrowth n (tailList pre post d sa sb) (realRank pre)
    d.weight.natAbs hp _ ?_
  intro h hh g
  refine realTaylorLeftPolynomial n (realPositionCharacter (tailList pre post d sa sb))
    (realRank pre) d.weight.natAbs hp (fun x hx => tailList_character_relation x hx) h
    h.2.1.1 ?_ g
  intro κ hκ
  rw [iterate_rightDerivative_rightTranslation hp h.2.1.1.1 κ]
  obtain ⟨Q, hQ, hQe⟩ := exists_poly_orbit hn hl hs h (LinearMap.mem_ker.mp hh) hκ
  have he : orbitFun hp (h : Langlands.GeneralLinear n ℝ → ℂ) κ = fun t : ℝ => Q.eval (t : ℂ) :=
    funext hQe
  rw [he]
  exact iteratedDeriv_eval_eq_zero hQ

end Tail

end RealTailKernel

end Langlands.Archimedean

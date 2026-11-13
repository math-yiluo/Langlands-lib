import Langlands.Representation.Conductor.ConductorMinimalityStatement
import Langlands.Representation.Conductor.SphericalLaurentFunctionalEquationStatement
import Langlands.Representation.Whittaker.MirabolicRestrictionInjectivityStatement
import Langlands.Representation.Conductor.EssentialRestrictionUniqueness
import Langlands.Representation.Conductor.EssentialDualSetup
import Langlands.Representation.Conductor.SphericalCompact
import Langlands.Representation.RankinSelberg.HighlyRamified.LastRowAgreement
import Langlands.Representation.RankinSelberg.LaurentEvaluation

/-!
# The conductor lower bound and scaled identity from the spherical functional equation

JPSS 1981, end of the proof of Theorem (5.1), printed pages 213–214. A Whittaker
function `W` fixed by `K(u)` vanishes on `diag(ϖ^λ, 1)` unless `λ` is dominant with
`λ_last ≥ 0`, so its corank-one integrals against `W(·; x; ψ̄)` are power series in
`q^(-s)` with constant term `W(1) vol(N\N K)`. Its dual function vanishes unless
`λ_last ≥ -u`. Comparing exponents through the spherical functional equation gives
`m ≤ u` for `W ≠ 0`, and a constant numerator at `u = m`.
-/

noncomputable section

namespace Langlands.Conductor

open Langlands.GeneralLinear Langlands.Whittaker Langlands.HarmonicAnalysis
open Langlands.RankinSelberg MeasureTheory Polynomial
open Langlands.GeneralLinear.Iwasawa Langlands.QuotientIntegration
open Langlands.Whittaker.UpperUnipotentCharacter (adjacentUnit)

universe uF uV

/-! ### Laurent expansions -/

section Laurent

/-- A Laurent series in `q^(-s)` with lower-bounded support whose sums vanish for all
large real `s` has zero coefficients. -/
theorem eq_zero_of_hasSum_spectralPoint {q : ℕ} (hq : 1 < q) {c : ℤ → ℂ} {d₀ : ℤ}
    (hc : ∀ d < d₀, c d = 0) {a : ℝ}
    (hsum : ∀ s : ℝ, a < s → HasSum (fun d : ℤ => c d * spectralPoint q (s : ℂ) ^ d) 0)
    (d : ℤ) : c d = 0 := by
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := lt_trans zero_lt_one hq1
  have hlogq : 0 < Real.log q := Real.log_pos hq1
  refine eq_zero_of_hasSum_int_eq_zero hc (Real.rpow_pos_of_pos hq0 (-a)) ?_ d
  intro X hX hXr
  set s : ℝ := -Real.log X / Real.log q with hsdef
  have hs : a < s := by
    have h1 : Real.log X < Real.log ((q : ℝ) ^ (-a)) := Real.log_lt_log hX hXr
    rw [Real.log_rpow hq0] at h1
    rw [hsdef, lt_div_iff₀ hlogq]
    linarith
  have hrpow : (q : ℝ) ^ (-s) = X := by
    rw [Real.rpow_def_of_pos hq0]
    have hl : Real.log q ≠ 0 := hlogq.ne'
    have hm : Real.log q * -s = Real.log X := by
      rw [hsdef]
      field_simp
    rw [hm, Real.exp_log hX]
  have hXs : spectralPoint q (s : ℂ) = (X : ℂ) := by
    rw [spectralPoint_ofReal, hrpow]
  simpa [hXs] using hsum s hs

/-- Multiplying a Laurent series by a polynomial convolves the coefficients. -/
theorem hasSum_polynomial_mul {e : ℤ → ℂ} {X S : ℂ} (hX : X ≠ 0)
    (he : HasSum (fun d : ℤ => e d * X ^ d) S) (P : ℂ[X]) :
    HasSum (fun d : ℤ => (∑ j ∈ P.support, P.coeff j * e (d - j)) * X ^ d)
      (P.eval X * S) := by
  have hterm : ∀ j ∈ P.support,
      HasSum (fun d : ℤ => P.coeff j * e (d - j) * X ^ d) (P.coeff j * X ^ j * S) := by
    intro j _
    have hshift : HasSum (fun d : ℤ => e (d - j) * X ^ (d - j)) S := by
      have := (Equiv.subRight (j : ℤ)).hasSum_iff.mpr he
      simpa [Function.comp_def] using this
    have hm := hshift.mul_left (P.coeff j * X ^ j)
    convert hm using 1
    funext d
    have hX' : X ^ d = X ^ (j : ℤ) * X ^ (d - j) := by
      rw [← zpow_add₀ hX]
      ring_nf
    rw [hX', zpow_natCast]
    ring
  have hsum := hasSum_sum hterm
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def, Finset.sum_mul]
  convert hsum using 1
  funext d
  rw [Finset.sum_mul]

/-- A Laurent polynomial is the sum of its monomials at a nonzero point. -/
theorem hasSum_laurentEval (Q : LaurentPolynomial ℂ) (x : ℂˣ) :
    HasSum (fun d : ℤ => Q.coeff d * (x : ℂ) ^ d) (laurentEval x Q) := by
  induction Q using LaurentPolynomial.induction_on' with
  | add p r hp hr =>
    rw [map_add]
    convert hp.add hr using 1
    funext d
    rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, add_mul]
  | C_mul_T k a =>
    rw [map_mul, laurentEval_C, laurentEval_T]
    have hcoeff : ∀ d : ℤ, (LaurentPolynomial.C a * LaurentPolynomial.T k).coeff d =
        if d = k then a else 0 := by
      intro d
      rw [← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single,
        Finsupp.single_apply]
      by_cases h : d = k
      · subst h
        simp
      · simp [h, Ne.symm h]
    convert hasSum_single k (f := fun d : ℤ =>
      (LaurentPolynomial.C a * LaurentPolynomial.T k).coeff d * (x : ℂ) ^ d) ?_ using 1
    · rw [hcoeff, ite_eq_left_iff.mpr (fun h => absurd rfl h)]
    · intro d hd
      rw [hcoeff, ite_eq_right_iff.mpr (fun h => absurd h hd), zero_mul]

end Laurent

/-! ### Matrices of the level subgroups -/

section Matrices

variable {F : Type uF} [Field F]

/-- The entries of `1 + y E_(i,i+1)`. -/
theorem adjacentUnit_val_apply {r : ℕ} (i : Fin r) (y : F) (a b : Fin (r + 1)) :
    (adjacentUnit i y).val a b =
      (if a = b then 1 else 0) + (if i.castSucc = a ∧ i.succ = b then y else 0) :=
  UpperUnipotentCharacter.transvection_apply _ _ _ _ _

/-- `(1 + y E_(i,i+1))⁻¹ = 1 - y E_(i,i+1)`. -/
theorem adjacentUnit_val_inv {r : ℕ} (i : Fin r) (y : F) :
    (adjacentUnit i y).val⁻¹ = (adjacentUnit i (-y)).val := by
  have h := UpperUnipotentCharacter.adjacentUnit_add i y (-y)
  rw [add_neg_cancel, UpperUnipotentCharacter.adjacentUnit_zero] at h
  rw [← Subgroup.coe_inv, eq_inv_of_mul_eq_one_right h.symm]

/-- `ᵗdiag(B,1)⁻¹ = diag(ᵗB⁻¹, 1)`. -/
theorem inverseTranspose_rankInclusion' {m : ℕ} (B : Langlands.GeneralLinear (m + 1) F) :
    inverseTranspose (m + 1 + 1) F (rankInclusion 1 B) =
      rankInclusion 1 (inverseTranspose (m + 1) F B) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [inverseTranspose_entry, ← map_inv]
  rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl <;>
    rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
  · rw [rankInclusion_castSucc_castSucc, rankInclusion_castSucc_castSucc,
      inverseTranspose_entry]
  · rw [rankInclusion_last_castSucc, rankInclusion_castSucc_last]
  · rw [rankInclusion_castSucc_last, rankInclusion_last_castSucc]
  · rw [rankInclusion_last_last, rankInclusion_last_last]

/-- `diag(ϖ^λ, 1) = ϖ^(λ, 0)`. -/
theorem rankInclusion_torus {m : ℕ} (ϖ : Fˣ) (lam : Fin m → ℤ) :
    rankInclusion 1 (torus ϖ lam) = torus ϖ (Fin.snoc lam 0) := by
  apply Units.ext
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [torus_val, Matrix.diagonal_apply, Ne.symm (Fin.castSucc_ne_last _),
      Fin.castSucc_ne_last]

variable [ValuativeRel F]

/-- `GL_(r+1)(O)` is stable under inverse transpose. -/
theorem inverseTranspose_mem_integralSubgroup' {r : ℕ} {k : Langlands.GeneralLinear (r + 1) F}
    (hk : k ∈ integralSubgroup (ValuativeRel.valuation F).integer r) :
    inverseTranspose (r + 1) F k ∈ integralSubgroup (ValuativeRel.valuation F).integer r := by
  rw [mem_integralSubgroup] at hk ⊢
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [inverseTranspose_entry]
    exact hk.2 j i
  · rw [← map_inv, inverseTranspose_entry, inv_inv]
    exact hk.1 j i

/-- `ϖ^a z` with `z` integral lies in the `a`-th power of the maximal ideal. -/
theorem exists_mem_maximalIdeal_pow {ϖ : Fˣ}
    (hϖ : IsUniformizingElement (ValuativeRel.valuation F) ϖ) (a : ℕ) {z : F}
    (hz : z ∈ (ValuativeRel.valuation F).integer) :
    ∃ x : (ValuativeRel.valuation F).integer,
      x ∈ IsLocalRing.maximalIdeal (ValuativeRel.valuation F).integer ^ a ∧
        (x : F) = (ϖ : F) ^ a * z := by
  refine ⟨jacquetUniformizerInteger (ValuativeRel.valuation F) ϖ hϖ ^ a * ⟨z, hz⟩, ?_, ?_⟩
  · rw [maximalIdeal_pow_eq_span_jacquetUniformizer (ValuativeRel.valuation F) ϖ hϖ a]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  · rfl

/-- The adjacent root `1 + z E_(n,n+1)` with `z` integral lies in every level subgroup. -/
theorem adjacentUnit_last_mem_levelSubgroup {n a : ℕ} {z : F}
    (hz : z ∈ (ValuativeRel.valuation F).integer) :
    (adjacentUnit (Fin.last n) z).val ∈ levelSubgroup F (n + 1) a := by
  have hK := (mem_integralSubgroup _ _ _).1
    (UnramifiedWhittaker.adjacentUnit_mem_integralSubgroup (v := ValuativeRel.valuation F)
      (Fin.last n) hz)
  refine RankinSelberg.HighlyRamified.mem_levelSubgroup_of_entries _ hK.1 hK.2 fun j => ?_
  refine ⟨0, Submodule.zero_mem _, ?_⟩
  change (0 : F) = (adjacentUnit (Fin.last n) z).val (Fin.last (n + 1)) j -
    (1 : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) F) (Fin.last (n + 1)) j
  rw [adjacentUnit_val_apply, Matrix.one_apply]
  have hne : (Fin.last n).castSucc ≠ Fin.last (n + 1) := Fin.castSucc_ne_last _
  simp [hne]

/-- The inverse transpose of `1 + ϖ^a z E_(n,n+1)` is the lower root
`1 - ϖ^a z E_(n+1,n)`, which lies in the level-`a` subgroup. -/
theorem inverseTranspose_adjacentUnit_last_mem_levelSubgroup {n a : ℕ} {ϖ : Fˣ}
    (hϖ : IsUniformizingElement (ValuativeRel.valuation F) ϖ) {z : F}
    (hz : z ∈ (ValuativeRel.valuation F).integer) :
    inverseTranspose (n + 1 + 1) F (adjacentUnit (Fin.last n) ((ϖ : F) ^ a * z)).val ∈
      levelSubgroup F (n + 1) a := by
  set y : F := (ϖ : F) ^ a * z with hy
  have hϖO : (ϖ : F) ∈ (ValuativeRel.valuation F).integer := hϖ.1.le
  have hyO : y ∈ (ValuativeRel.valuation F).integer :=
    Subring.mul_mem _ (Subring.pow_mem _ hϖO a) hz
  have hentry : ∀ (t : F), t ∈ (ValuativeRel.valuation F).integer → ∀ i j,
      (adjacentUnit (Fin.last n) t).val i j ∈ (ValuativeRel.valuation F).integer := by
    intro t ht i j
    rw [adjacentUnit_val_apply]
    refine Subring.add_mem _ ?_ ?_
    · split_ifs
      · exact Subring.one_mem _
      · exact Subring.zero_mem _
    · split_ifs
      · exact ht
      · exact Subring.zero_mem _
  apply RankinSelberg.HighlyRamified.mem_levelSubgroup_of_entries
  · intro i j
    rw [inverseTranspose_entry, adjacentUnit_val_inv]
    exact hentry _ (Subring.neg_mem _ hyO) j i
  · intro i j
    rw [← map_inv, inverseTranspose_entry, inv_inv]
    exact hentry _ hyO j i
  · intro j
    obtain ⟨x, hx, hxe⟩ := exists_mem_maximalIdeal_pow hϖ a (Subring.neg_mem _ hz)
    have hrow : inverseTranspose (n + 1 + 1) F (adjacentUnit (Fin.last n) y).val
        (Fin.last (n + 1)) j - (1 : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) F)
          (Fin.last (n + 1)) j =
        if (Fin.last n).castSucc = j then -y else 0 := by
      rw [inverseTranspose_entry, adjacentUnit_val_inv, adjacentUnit_val_apply,
        Matrix.one_apply]
      have hs : (Fin.last n).succ = Fin.last (n + 1) := Fin.succ_last n
      by_cases hj : (Fin.last n).castSucc = j
      · subst hj
        simp [hs, Fin.castSucc_ne_last, Ne.symm (Fin.castSucc_ne_last _)]
      · by_cases hjl : j = Fin.last (n + 1)
        · subst hjl
          simp [hs]
        · simp [hj, hjl, Ne.symm hjl]
    rw [hrow]
    split_ifs
    · exact ⟨x, hx, by rw [hxe, hy]; ring⟩
    · exact ⟨0, Submodule.zero_mem _, rfl⟩

end Matrices

/-! ### Support of level-fixed Whittaker functions on the torus -/

section Support

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F] {n : ℕ}

/-- Let `W` be a `ψ'`-Whittaker function on `GL_(n+2)` with `ψ'` of conductor `O`,
whose restriction to `diag(GL_(n+1), 1)` is right `GL_(n+1)(O)`-invariant and which is
right invariant under `1 + ϖ^b z E_(n,n+1)` for integral `z`. If `W(diag(ϖ^λ, 1)) ≠ 0`,
then `λ` is dominant and `λ_n ≥ -b`. -/
theorem torus_support_of_invariant {ψ' : UnitaryAdditiveCharacter F}
    (hψ' : HasIntegerConductor ψ') {ϖ : Fˣ}
    (hϖ : IsUniformizingElement (ValuativeRel.valuation F) ϖ) (b : ℕ)
    (W : WhittakerFunctions ψ' (n + 1))
    (hK : ∀ g : Langlands.GeneralLinear (n + 1) F,
      ∀ k ∈ integralSubgroup (ValuativeRel.valuation F).integer n,
        W.val (rankInclusion 1 (g * k)) = W.val (rankInclusion 1 g))
    (hU : ∀ g : Langlands.GeneralLinear ((n + 1) + 1) F,
      ∀ z ∈ (ValuativeRel.valuation F).integer,
        W.val (g * (adjacentUnit (Fin.last n) ((ϖ : F) ^ b * z)).val) = W.val g)
    (lam : Fin (n + 1) → ℤ) (hW : W.val (rankInclusion 1 (torus ϖ lam)) ≠ 0) :
    Antitone lam ∧ -(b : ℤ) ≤ lam (Fin.last n) := by
  constructor
  · by_contra hlam
    apply hW
    have hf : ∀ (u : upperUnipotent (n + 1) F) (g : Langlands.GeneralLinear (n + 1) F),
        W.val (rankInclusion 1 (u.val * g)) =
          (standardCharacter ψ' n u : ℂ) * W.val (rankInclusion 1 g) := by
      intro u g
      rw [map_mul]
      change W.val ((corankOneUnipotent u).val * rankInclusion 1 g) = _
      rw [W.property, corankOne_standardCharacter]
    have hθ : ∀ i : Fin n, ∃ x : F,
        ValuativeRel.valuation F x * ValuativeRel.valuation F (ϖ : F) ≤ 1 ∧
          standardCharacter ψ' n (adjacentUnit i x) ≠ 1 := by
      intro i
      have hv0 : 0 < ValuativeRel.valuation F (ϖ : F) :=
        valuation_pos (ValuativeRel.valuation F) ϖ
      have hnot : ((ϖ : F))⁻¹ ∉ (ValuativeRel.valuation F).integer := by
        rw [Valuation.mem_integer_iff, map_inv₀, not_le]
        exact one_lt_inv_iff₀.mpr ⟨hv0, hϖ.1⟩
      have hex : ∃ y ∈ (ValuativeRel.valuation F).integer, ψ' ((ϖ : F)⁻¹ * y) ≠ 1 := by
        by_contra hall
        push Not at hall
        exact hnot (hψ'.2 _ hall)
      obtain ⟨y, hy, hψy⟩ := hex
      refine ⟨(ϖ : F)⁻¹ * y, ?_, ?_⟩
      · rw [map_mul, map_inv₀, mul_comm, ← mul_assoc, mul_inv_cancel₀ hv0.ne', one_mul]
        exact hy
      · intro h1
        apply hψy
        have h2 := congrArg (fun z : ℂˣ => (z : ℂ)) h1
        simp only [standardCharacter_adjacentUnit_val, UnitaryAdditiveCharacter.complex_apply,
          Units.val_one] at h2
        exact Subtype.ext (by rw [h2, Circle.coe_one])
    exact UnramifiedWhittaker.eval_torus_eq_zero_of_not_antitone hϖ
      (f := fun g => W.val (rankInclusion 1 g)) hf hK hθ hlam
  · set T := rankInclusion 1 (torus ϖ lam) with hT
    set l := lam (Fin.last n) with hl
    have hconj : ∀ y : F, T⁻¹ * (adjacentUnit (Fin.last n) (((ϖ ^ l : Fˣ) : F) * y)).val * T =
        (adjacentUnit (Fin.last n) y).val := by
      intro y
      rw [hT, rankInclusion_torus]
      have h := UnramifiedWhittaker.torus_inv_conj_adjacentUnit (F := F) (ϖ := ϖ)
        (Fin.snoc lam 0 : Fin (n + 1 + 1) → ℤ) (Fin.last n) (((ϖ ^ l : Fˣ) : F) * y)
      rw [h]
      congr 2
      rw [Fin.succ_last, Fin.snoc_last, Fin.snoc_castSucc, zpow_zero, Units.val_one, mul_one,
        ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
    have hchar : ∀ z ∈ (ValuativeRel.valuation F).integer,
        ψ' (((ϖ ^ l : Fˣ) : F) * ((ϖ : F) ^ b * z)) = 1 := by
      intro z hz
      set y := (ϖ : F) ^ b * z
      set x := ((ϖ ^ l : Fˣ) : F) * y
      have hmove : (adjacentUnit (Fin.last n) x).val * T =
          T * (adjacentUnit (Fin.last n) y).val := by
        rw [← hconj y, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
      have h1 := W.property (adjacentUnit (Fin.last n) x) T
      rw [hmove, hU T z hz, standardCharacter_adjacentUnit_val] at h1
      have h2 : ψ'.complex x = 1 := by
        have := mul_right_cancel₀ hW (h1.symm.trans (one_mul _).symm)
        exact this
      apply Subtype.ext
      simpa only [UnitaryAdditiveCharacter.complex_apply, Circle.coe_one] using h2
    have hint : ((ϖ ^ (l + (b : ℤ)) : Fˣ) : F) ∈ (ValuativeRel.valuation F).integer := by
      apply hψ'.2
      intro z hz
      have he : ((ϖ ^ (l + (b : ℤ)) : Fˣ) : F) * z =
          ((ϖ ^ l : Fˣ) : F) * ((ϖ : F) ^ b * z) := by
        rw [zpow_add, Units.val_mul, zpow_natCast, Units.val_pow_eq_pow_val, mul_assoc]
      rw [he]
      exact hchar z hz
    have := (uniformizer_zpow_mem_integer_iff hϖ _).mp hint
    omega

/-- Under the hypotheses of `torus_support_of_invariant`, the corank-one integrand of
`W` vanishes at every quotient point whose Iwasawa exponent is not dominant with last
coordinate at least `-b`. -/
theorem quotientExponent_support_of_integrand_ne_zero {ψ' : UnitaryAdditiveCharacter F}
    {ϖ : Fˣ} (hϖ : IsUniformizingElement (ValuativeRel.valuation F) ϖ) (b : ℕ)
    (abv : AbsoluteValue F ℝ) (W : WhittakerFunctions ψ' (n + 1))
    (W' : InverseWhittakerFunctions ψ' n)
    (hK : ∀ g : Langlands.GeneralLinear (n + 1) F,
      ∀ k ∈ integralSubgroup (ValuativeRel.valuation F).integer n,
        W.val (rankInclusion 1 (g * k)) = W.val (rankInclusion 1 g))
    (hsupp : ∀ lam : Fin (n + 1) → ℤ, W.val (rankInclusion 1 (torus ϖ lam)) ≠ 0 →
      Antitone lam ∧ -(b : ℤ) ≤ lam (Fin.last n))
    (s : ℂ) (t : LeftUnipotentQuotient n F)
    (ht : corankOneIntegrand ψ' abv W W' s t ≠ 0) :
    Antitone (quotientExponent hϖ t) ∧ -(b : ℤ) ≤ quotientExponent hϖ t (Fin.last n) := by
  induction t using Quotient.inductionOn with
  | h g =>
    rw [quotientExponent_mk]
    obtain ⟨u, hu, k, hk, heq⟩ := exists_eq_exponent hϖ g
    apply hsupp
    intro h0
    apply ht
    have hWg : W.val (rankInclusion 1 g) = 0 := by
      rw [heq, mul_assoc, map_mul]
      change W.val ((corankOneUnipotent ⟨u, hu⟩).val *
        rankInclusion 1 (torus ϖ (exponent hϖ g) * k)) = 0
      rw [W.property, hK _ k hk, h0, mul_zero]
    rw [corankOneIntegrand_mk, hWg, zero_mul, zero_mul]

/-- `Σ λ_i ≥ (n + 1) λ_n` for antitone `λ`. -/
theorem sum_ge_of_antitone {lam : Fin (n + 1) → ℤ} (hlam : Antitone lam) :
    ((n + 1 : ℕ) : ℤ) * lam (Fin.last n) ≤ ∑ i, lam i := by
  calc ((n + 1 : ℕ) : ℤ) * lam (Fin.last n) = ∑ _i : Fin (n + 1), lam (Fin.last n) := by
        simp
    _ ≤ ∑ i, lam i := Finset.sum_le_sum fun i _ => hlam (Fin.le_last i)

end Support

/-! ### Degree coefficients -/

section Degree

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {n : ℕ}
  [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
  [BorelSpace (Langlands.GeneralLinear (n + 1) F)]
  [MeasurableSpace (upperUnipotent (n + 1) F)] [BorelSpace (upperUnipotent (n + 1) F)]
  [MeasurableSpace (LeftUnipotentQuotient n F)] [MeasurableSpace (LeftUnipotentQuotient 0 F)]
  {q : ℕ} {ψ' : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ} {ϖ : Fˣ}
  {μ : Measure (LeftUnipotentQuotient n F)}

/-- The degree-`d` integral of the integrand at `s = 0`, the `d`-th Laurent
coefficient in `hasSum_corankOneIntegral`. -/
def degreeIntegral (h' : IsJacquetNormalization q ψ' abv ϖ μ)
    (W : WhittakerFunctions ψ' (n + 1)) (W' : InverseWhittakerFunctions ψ' n) (d : ℤ) : ℂ :=
  ∫ t, (if sphericalQuotientDegree h'.uniformizer t = d then
    corankOneIntegrand ψ' abv W W' 0 t else 0) ∂μ

/-- The degree integrals vanish below `-(n + 1) b` under the support condition with
bound `b`. -/
theorem degreeIntegral_eq_zero_of_lt (h' : IsJacquetNormalization q ψ' abv ϖ μ)
    (W : WhittakerFunctions ψ' (n + 1)) (W' : InverseWhittakerFunctions ψ' n) (b : ℕ)
    (hK : ∀ g : Langlands.GeneralLinear (n + 1) F,
      ∀ k ∈ integralSubgroup (ValuativeRel.valuation F).integer n,
        W.val (rankInclusion 1 (g * k)) = W.val (rankInclusion 1 g))
    (hsupp : ∀ lam : Fin (n + 1) → ℤ, W.val (rankInclusion 1 (torus ϖ lam)) ≠ 0 →
      Antitone lam ∧ -(b : ℤ) ≤ lam (Fin.last n))
    {d : ℤ} (hd : d < -(((n + 1 : ℕ) : ℤ) * b)) :
    degreeIntegral h' W W' d = 0 := by
  have hzero : (fun t => if sphericalQuotientDegree h'.uniformizer t = d then
      corankOneIntegrand ψ' abv W W' 0 t else 0) = fun _ => 0 := by
    funext t
    split_ifs with ht
    · by_contra hne
      obtain ⟨hanti, hlast⟩ := quotientExponent_support_of_integrand_ne_zero
        h'.uniformizer b abv W W' hK hsupp 0 t hne
      have hsum := sum_ge_of_antitone hanti
      rw [← sphericalQuotientDegree_eq_sum, ht] at hsum
      have : ((n + 1 : ℕ) : ℤ) * (-(b : ℤ)) ≤ ((n + 1 : ℕ) : ℤ) * quotientExponent
          h'.uniformizer t (Fin.last n) :=
        mul_le_mul_of_nonneg_left hlast (by positivity)
      linarith
    · rfl
  rw [degreeIntegral, hzero, integral_zero]

/-- For a spherical test and the support condition with bound `0`, the degree-zero
integral is `vol(N \ N K) W(1)`. -/
theorem degreeIntegral_zero_eq (h : IsJacquetNormalization q ψ' abv ϖ μ)
    (W : WhittakerFunctions ψ' (n + 1))
    (hK : ∀ g : Langlands.GeneralLinear (n + 1) F,
      ∀ k ∈ integralSubgroup (ValuativeRel.valuation F).integer n,
        W.val (rankInclusion 1 (g * k)) = W.val (rankInclusion 1 g))
    (hsupp : ∀ lam : Fin (n + 1) → ℤ, W.val (rankInclusion 1 (torus ϖ lam)) ≠ 0 →
      Antitone lam ∧ -((0 : ℕ) : ℤ) ≤ lam (Fin.last n))
    (x : Fin (n + 1) → ℂˣ) :
    degreeIntegral h W (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x) 0 =
      μ.real (sphericalCell h.uniformizer 0) * W.val 1 := by
  let : BorelSpace (LeftUnipotentQuotient n F) := h.borel
  have hq : 0 < q := lt_trans zero_lt_one h.one_lt_q
  have htorus0 : torus ϖ (0 : Fin (n + 1) → ℤ) = 1 := by
    rw [torus]
    convert map_one (diagonalUnits (F := F) (m := n + 1)) using 2
    funext i
    simp
  have hfun : (fun t => if sphericalQuotientDegree h.uniformizer t = 0 then
      corankOneIntegrand ψ' abv W (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x)
        0 t else 0) =
      (sphericalCell h.uniformizer 0).indicator (fun _ => W.val 1) := by
    funext t
    by_cases hcell : t ∈ sphericalCell h.uniformizer (0 : Fin (n + 1) → ℤ)
    · rw [Set.indicator_of_mem hcell]
      have hdeg : sphericalQuotientDegree h.uniformizer t = 0 := by
        rw [sphericalQuotientDegree_eq_sum, (mem_sphericalCell_iff _).1 hcell]
        simp
      simp only [hdeg, ↓reduceIte]
      rw [sphericalCell_eq_image] at hcell
      obtain ⟨k, hk, rfl⟩ := hcell
      change corankOneIntegrand ψ' abv W _ 0 (Quotient.mk _ (torus ϖ 0 * k)) = _
      rw [corankOneIntegrand_mk, htorus0, one_mul]
      have hW1 : W.val (rankInclusion 1 k) = W.val 1 := by
        have := hK 1 k hk
        rwa [one_mul, map_one] at this
      have hW' : (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x).val k = 1 := by
        have := inverseSphericalWhittaker_mul_integral h.conductor.1 h.uniformizer q x 1 hk
        rwa [one_mul, inverseSphericalWhittaker_one] at this
      have hexp : exponent h.uniformizer k = 0 := by
        have h1 := exponent_mul_integral h.uniformizer (1 : Langlands.GeneralLinear (n + 1) F) hk
        rw [one_mul, ← htorus0, exponent_torus] at h1
        exact h1
      rw [hW1, hW', determinantWeight_eq_degree_power abv h.uniformizer h.abv_unit q hq
        h.abv_uniformizer k, hexp]
      simp
    · rw [Set.indicator_of_notMem hcell]
      split_ifs with hdeg
      · by_contra hne
        apply hcell
        obtain ⟨hanti, hlast⟩ := quotientExponent_support_of_integrand_ne_zero
          h.uniformizer 0 abv W _ hK hsupp 0 t hne
        rw [mem_sphericalCell_iff]
        have hnonneg : ∀ i, 0 ≤ quotientExponent h.uniformizer t i := fun i =>
          le_trans (by simpa using hlast) (hanti (Fin.le_last i))
        rw [sphericalQuotientDegree_eq_sum] at hdeg
        funext i
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnonneg i)).1 hdeg i
          (Finset.mem_univ i)
      · rfl
  rw [degreeIntegral, hfun, integral_indicator_const _
    (isOpen_sphericalCell h.uniformizer 0).measurableSet, Complex.real_smul]

end Degree

/-! ### Exponent bounds for the numerator -/

section Numerator

variable {q : ℕ}

/-- If `f(s) = ∑_(d ≥ 0) e_d q^(-ds)` on a real half-line and `f` continues to `R` with
`Q = D R` for a Laurent polynomial `Q` and a polynomial `D` with `D(0) = 1`, then `Q`
has no negative exponents and constant coefficient `e_0`. -/
theorem laurent_coeff_of_forward (hq : 1 < q) {f : ℂ → ℂ} {e : ℤ → ℂ}
    (he : ∀ d < 0, e d = 0) {a : ℝ}
    (hsum : ∀ s : ℝ, a < s → HasSum (fun d : ℤ => spectralPoint q (s : ℂ) ^ d * e d) (f s))
    {D : ℂ[X]} (hD : D.coeff 0 = 1) {Q : LaurentPolynomial ℂ} {R : RationalFunctions}
    (hQR : laurentToRatFunc Q = algebraMap ℂ[X] RationalFunctions D * R)
    (hR : HasRationalContinuation q f R) :
    (∀ d < 0, Q.coeff d = 0) ∧ Q.coeff 0 = e 0 := by
  obtain ⟨aR, hR⟩ := hR
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  set conv : ℤ → ℂ := fun d => ∑ j ∈ D.support, D.coeff j * e (d - j) with hconv
  have hconv0 : ∀ d < 0, conv d = 0 := by
    intro d hd
    apply Finset.sum_eq_zero
    intro j _
    rw [he _ (by omega), mul_zero]
  have hkey : ∀ d, Q.coeff d - conv d = 0 := by
    obtain ⟨L, hL⟩ := Q.coeff.support.bddBelow
    refine eq_zero_of_hasSum_spectralPoint hq (d₀ := min L 0) ?_ (a := max a aR) ?_
    · intro d hd
      have hQd : Q.coeff d = 0 := by
        by_contra hne
        have := hL (Finsupp.mem_support_iff.mpr hne)
        omega
      rw [hQd, hconv0 d (by omega), sub_zero]
    · intro s hs
      have hsa : a < s := lt_of_le_of_lt (le_max_left _ _) hs
      have hsR : aR < (s : ℂ).re := by
        rw [Complex.ofReal_re]
        exact lt_of_le_of_lt (le_max_right _ _) hs
      obtain ⟨hden, hfR⟩ := hR s hsR
      set X := spectralPoint q (s : ℂ) with hX
      have hX0 : X ≠ 0 := spectralPoint_ne_zero_of_pos hq0 _
      have hlaur := laurentEval_eq_of_laurentToRatFunc_eq (spectralUnit hq0 (s : ℂ)) hQR
        (by simpa using hden)
      have h1 := hasSum_laurentEval Q (spectralUnit hq0 (s : ℂ))
      simp only [coe_spectralUnit] at h1 hlaur
      have h2 := hasSum_polynomial_mul hX0
        (by simpa only [mul_comm] using hsum s hsa) D
      rw [hfR, ← hlaur] at h2
      have h3 := h1.sub h2
      rw [sub_self] at h3
      convert h3 using 1
      funext d
      rw [sub_mul]
  refine ⟨fun d hd => ?_, ?_⟩
  · have := hkey d
    rw [hconv0 d hd, sub_zero] at this
    exact this
  · have h0 := hkey 0
    rw [sub_eq_zero] at h0
    rw [h0, hconv]
    simp only
    rw [Finset.sum_eq_single 0]
    · rw [hD, one_mul]
      simp
    · intro j _ hj
      rw [he _ (by omega), mul_zero]
    · intro h0'
      exact absurd (Polynomial.notMem_support_iff.mp h0') (by rw [hD]; exact one_ne_zero)

/-- If `fd(s) = ∑_(d ≥ -B) ẽ_d q^(-ds)` on a real half-line, `fd` continues to `Rd`, and
`Dd(q^(-(1-s))) Rd(q^(-(1-s))) = ζ^e c q^(-Ms) D(q^(-s)) R(q^(-s))` with `Q = D R`, then
every exponent `k` of the Laurent polynomial `Q` satisfies `k ≤ B - M`. -/
theorem laurent_coeff_of_dual (hq : 1 < q) {fd : ℂ → ℂ} {ed : ℤ → ℂ} {B : ℤ}
    (hed : ∀ d < -B, ed d = 0) {a : ℝ}
    (hsum : ∀ s : ℝ, a < s →
      HasSum (fun d : ℤ => spectralPoint q (s : ℂ) ^ d * ed d) (fd s))
    {D Dd : ℂ[X]} {ζ c : ℂˣ} {e : ℕ} {M : ℤ} {Q : LaurentPolynomial ℂ}
    {R Rd : RationalFunctions}
    (hQR : laurentToRatFunc Q = algebraMap ℂ[X] RationalFunctions D * R)
    (hRd : HasRationalContinuation q fd Rd)
    (hFE : NormalizedFunctionalEquation q D Dd ζ c e M R Rd) :
    ∀ k, Q.coeff k ≠ 0 → k ≤ B - M := by
  obtain ⟨ad, hRd⟩ := hRd
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq0.ne'
  obtain ⟨aB, haB⟩ := (finite_reflected_spectralPoint_roots hq (RatFunc.denom_ne_zero R)).bddAbove
  set conv : ℤ → ℂ := fun d => ∑ j ∈ Dd.support, Dd.coeff j * ed (d - j) with hconv
  have hconv0 : ∀ d < -B, conv d = 0 := by
    intro d hd
    apply Finset.sum_eq_zero
    intro j _
    rw [hed _ (by omega), mul_zero]
  set lhs : ℤ → ℂ := fun d => (ζ : ℂ) ^ e * (c : ℂ) * Q.coeff (-M - d) * (q : ℂ) ^ d
    with hlhs
  have hkey : ∀ d, lhs d - conv d = 0 := by
    obtain ⟨U, hU⟩ := Q.coeff.support.bddAbove
    refine eq_zero_of_hasSum_spectralPoint hq (d₀ := min (-B) (-M - U)) ?_
      (a := max a (max ad aB)) ?_
    · intro d hd
      have hQd : Q.coeff (-M - d) = 0 := by
        by_contra hne
        have := hU (Finsupp.mem_support_iff.mpr hne)
        omega
      rw [hlhs]
      simp only
      rw [hQd, hconv0 d (by omega)]
      ring
    · intro s hs
      have hsa : a < s := lt_of_le_of_lt (le_max_left _ _) hs
      have hsd : ad < (s : ℂ).re := by
        rw [Complex.ofReal_re]
        exact lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hs
      have hsB : aB < s := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hs
      obtain ⟨hdend, hfd⟩ := hRd s hsd
      have hcond1 : R.denom.eval (spectralPoint q (1 - (s : ℂ))) ≠ 0 := by
        intro h0
        have := haB (show s ∈ {t : ℝ | R.denom.eval (spectralPoint q (1 - (t : ℂ))) = 0}
          from h0)
        linarith
      have hcond2 : Rd.denom.eval (spectralPoint q (1 - (1 - (s : ℂ)))) ≠ 0 := by
        rw [sub_sub_cancel]
        exact hdend
      have hfe := hFE (1 - (s : ℂ)) hcond1 hcond2
      rw [sub_sub_cancel] at hfe
      set X' := spectralPoint q (s : ℂ) with hX'
      set X := spectralPoint q (1 - (s : ℂ)) with hX
      have hX'0 : X' ≠ 0 := spectralPoint_ne_zero_of_pos hq0 _
      have hX0 : X ≠ 0 := spectralPoint_ne_zero_of_pos hq0 _
      have hXX' : X = (q : ℂ)⁻¹ * X'⁻¹ := spectralPoint_sub_one_sub hq0 _
      have hlaur := laurentEval_eq_of_laurentToRatFunc_eq (spectralUnit hq0 (1 - (s : ℂ)))
        hQR (by simpa using hcond1)
      simp only [coe_spectralUnit] at hlaur
      rw [← hlaur] at hfe
      unfold epsilonMonomial at hfe
      -- left side as a Laurent series in `X'`
      have hL := hasSum_polynomial_mul hX'0 (by simpa only [mul_comm] using hsum s hsa) Dd
      rw [hfd, hfe] at hL
      -- right side as a Laurent series in `X'`
      have hR1 := (hasSum_laurentEval Q (spectralUnit hq0 (1 - (s : ℂ)))).mul_left
        ((ζ : ℂ) ^ e * ((c : ℂ) * X ^ M))
      simp only [coe_spectralUnit] at hR1
      have hR2 := (Equiv.subLeft (-M)).hasSum_iff.mpr hR1
      have hR3 : HasSum (fun d : ℤ => lhs d * X' ^ d)
          ((ζ : ℂ) ^ e * ((c : ℂ) * X ^ M) *
            laurentEval (spectralUnit hq0 (1 - (s : ℂ))) Q) := by
        convert hR2 using 1
        funext d
        simp only [Function.comp_apply, Equiv.subLeft_apply, hlhs]
        have hpow : X ^ M * X ^ (-M - d) = (q : ℂ) ^ d * X' ^ d := by
          rw [← zpow_add₀ hX0, show M + (-M - d) = -d by ring, hXX', ← mul_inv,
            inv_zpow', neg_neg, mul_zpow]
        calc (ζ : ℂ) ^ e * (c : ℂ) * Q.coeff (-M - d) * (q : ℂ) ^ d * X' ^ d
            = (ζ : ℂ) ^ e * (c : ℂ) * Q.coeff (-M - d) * ((q : ℂ) ^ d * X' ^ d) := by ring
          _ = (ζ : ℂ) ^ e * (c : ℂ) * Q.coeff (-M - d) * (X ^ M * X ^ (-M - d)) := by
            rw [hpow]
          _ = _ := by ring
      have h3 := hR3.sub hL
      rw [mul_assoc, sub_self] at h3
      convert h3 using 1
      funext d
      rw [sub_mul]
  intro k hk
  by_contra hlt
  push Not at hlt
  have h := hkey (-M - k)
  rw [hconv0 _ (by omega), sub_zero, hlhs] at h
  simp only [show -M - (-M - k) = k by ring] at h
  have hne : (ζ : ℂ) ^ e * (c : ℂ) * Q.coeff k * (q : ℂ) ^ (-M - k) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ ζ.ne_zero) c.ne_zero) hk)
      (zpow_ne_zero _ hqC)
  exact hne h

end Numerator

/-! ### Assembly -/

section Assembly

/-- The polynomial `∏ i, P(x_i X)` has constant term one when `P` does. -/
theorem prod_comp_coeff_zero {m : ℕ} {P : ℂ[X]} (hP : P.coeff 0 = 1) (x : Fin m → ℂˣ) :
    (∏ i, P.comp (C (x i : ℂ) * X)).coeff 0 = 1 := by
  rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_prod]
  apply Finset.prod_eq_one
  intro i _
  rw [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    mul_zero, ← Polynomial.coeff_zero_eq_eval_zero, hP]

/-- `Q` is `∏ i, P(x_i X)` times `Q · essentialFactor P x`. -/
theorem laurentToRatFunc_eq_mul_essentialFactor {m : ℕ} {P : ℂ[X]} (hP : P.coeff 0 = 1)
    (x : Fin m → ℂˣ) (Q : LaurentPolynomial ℂ) :
    laurentToRatFunc Q = algebraMap ℂ[X] RationalFunctions (∏ i, P.comp (C (x i : ℂ) * X)) *
      (laurentToRatFunc Q * essentialFactor P x) := by
  have hD : (∏ i, P.comp (C (x i : ℂ) * X)) ≠ 0 := by
    intro h0
    have := prod_comp_coeff_zero hP x
    rw [h0, Polynomial.coeff_zero] at this
    exact zero_ne_one this
  rw [essentialFactor_eq, mul_comm (laurentToRatFunc Q), ← mul_assoc,
    mul_inv_cancel₀ (RatFunc.algebraMap_ne_zero hD), one_mul]

/-- **Reduction.** The spherical corank-one functional equation and mirabolic
restriction injectivity imply the JPSS conductor lower bound and scaled identity. -/
theorem conductorMinimalityStatement_of_sphericalFunctionalEquation
    (hFE : SphericalLaurentFunctionalEquationStatement.{uF, uV})
    (hinj : Whittaker.MirabolicRestrictionInjectivityStatement.{uF, uV}) :
    ConductorMinimalityStatement.{uF, uV} := by
  intro F _ _ _ _ _ _ _ _ n _ _ _ _ _ _ _ _ _ _ q ψ abv ϖ μ h ν hν V _ _ π hπ ℓ hℓ P hP
    c m hε u v hv
  obtain ⟨Pdual, -, hall⟩ := hFE F n q ψ abv ϖ μ h ν hν π hπ ℓ hℓ P hP c m hε
  have hq : 1 < q := h.one_lt_q
  have hP1 : P.coeff 0 = 1 := hP.1
  have hres : IsIntegralInvariantOnRestriction π ℓ v :=
    isIntegralInvariantOnRestriction_of_mem_levelFixedVectors π ℓ v hv
  have hfix : ∀ (y k : Langlands.GeneralLinear ((n + 1) + 1) F),
      k ∈ levelSubgroup F (n + 1) u → v.val.val (y * k) = v.val.val y := by
    intro y k hk
    have he : modelRepresentation π ℓ k v = v := hv ⟨k, hk⟩
    exact congrArg (fun z : (coefficientModel π ℓ).toSubmodule => z.val.val y) he
  -- forward support
  have hKF : ∀ g : Langlands.GeneralLinear (n + 1) F,
      ∀ k ∈ integralSubgroup (ValuativeRel.valuation F).integer n,
        v.val.val (rankInclusion 1 (g * k)) = v.val.val (rankInclusion 1 g) :=
    fun g k hk => hres g ⟨k, hk⟩
  have hsuppF := torus_support_of_invariant h.conductor h.uniformizer 0 v.val hKF
    (fun g z hz => by
      rw [pow_zero, one_mul]
      exact hfix g _ (adjacentUnit_last_mem_levelSubgroup hz))
  -- dual support
  set Wd := firstDualFunction ψ (n + 1) v.val with hWd
  have hWd_apply : ∀ y, Wd.val y =
      v.val.val (weylLong ((n + 1) + 1) F * inverseTranspose ((n + 1) + 1) F y) :=
    fun y => rfl
  have hKD : ∀ g : Langlands.GeneralLinear (n + 1) F,
      ∀ k ∈ integralSubgroup (ValuativeRel.valuation F).integer n,
        Wd.val (rankInclusion 1 (g * k)) = Wd.val (rankInclusion 1 g) := by
    intro g k hk
    rw [hWd_apply, hWd_apply, map_mul, map_mul, ← mul_assoc]
    apply hfix
    rw [inverseTranspose_rankInclusion']
    exact rankInclusion_mem_congruenceSubgroup _ _ _
      ⟨_, inverseTranspose_mem_integralSubgroup' hk⟩
  have hsuppD := torus_support_of_invariant (hasIntegerConductor_scale_neg_one h.conductor)
    h.uniformizer u Wd hKD (fun g z hz => by
      rw [hWd_apply, hWd_apply, map_mul, ← mul_assoc]
      exact hfix _ _ (inverseTranspose_adjacentUnit_last_mem_levelSubgroup h.uniformizer hz))
  -- the analysis for one Satake parameter
  have hx : ∀ x : Fin (n + 1) → ℂˣ,
      (∃ a : ℝ, ∀ s : ℂ, a < s.re →
        CorankOneConverges ψ abv μ v.val
          (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x) s) ∧
      ∃ Q : LaurentPolynomial ℂ,
        HasRationalContinuation q
          (corankOneIntegral ψ abv μ v.val
            (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x))
          (laurentToRatFunc Q * essentialFactor P x) ∧
        (∀ d < 0, Q.coeff d = 0) ∧
        Q.coeff 0 = μ.real (sphericalCell h.uniformizer 0) * v.val.val 1 ∧
        ∀ k, Q.coeff k ≠ 0 → k ≤ ((n + 1 : ℕ) : ℤ) * u - ((n + 1 : ℕ) : ℤ) * m := by
    intro x
    obtain ⟨⟨a₁, hcv⟩, ⟨a₂, hcvd⟩, Q, Rdual, hRQ, hRd, hNFE⟩ := hall v x
    refine ⟨⟨a₁, hcv⟩, Q, hRQ, ?_⟩
    have hQR := laurentToRatFunc_eq_mul_essentialFactor hP1 x Q
    have hfw := laurent_coeff_of_forward hq
      (e := degreeIntegral h v.val (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x))
      (fun d hd => degreeIntegral_eq_zero_of_lt h _ _ 0 hKF hsuppF (by simpa using hd))
      (a := a₁) (fun s hs => hasSum_corankOneIntegral h v.val _ (s : ℂ)
        (hcv s (by simpa using hs)))
      (prod_comp_coeff_zero hP1 x) hQR hRQ
    have hdual := laurent_coeff_of_dual hq
      (ed := degreeIntegral h.scaleNegOne Wd
        (secondDualFunction ψ n (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x)))
      (B := ((n + 1 : ℕ) : ℤ) * u)
      (fun d hd => degreeIntegral_eq_zero_of_lt h.scaleNegOne _ _ u hKD hsuppD (by omega))
      (a := a₂) (fun s hs => hasSum_corankOneIntegral h.scaleNegOne Wd _ (s : ℂ)
        (hcvd s (by simpa using hs)))
      hQR hRd hNFE
    refine ⟨hfw.1, ?_, hdual⟩
    rw [hfw.2]
    exact degreeIntegral_zero_eq h v.val hKF hsuppF x
  refine ⟨fun hv0 => ?_, fun hum => ?_⟩
  · by_contra hlt
    push Not at hlt
    apply hv0
    have hzero : ∀ x : Fin (n + 1) → ℂˣ, ∃ a : ℝ, ∀ s : ℝ, a < s →
        CorankOneConverges ψ abv μ v.val
            (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x) s ∧
          corankOneIntegral ψ abv μ v.val
            (inverseSphericalWhittaker h.conductor.1 h.uniformizer q x) s = 0 := by
      intro x
      obtain ⟨⟨a₁, hcv⟩, Q, ⟨aR, hR⟩, hneg, -, hbound⟩ := hx x
      have hQ : Q = 0 := by
        apply LaurentPolynomial.ext
        intro k
        rw [AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply]
        by_contra hk
        have hk' := hbound k hk
        have hkneg : k < 0 := by
          have : ((n + 1 : ℕ) : ℤ) * u < ((n + 1 : ℕ) : ℤ) * m :=
            mul_lt_mul_of_pos_left hlt (by positivity)
          omega
        exact hk (hneg k hkneg)
      refine ⟨max a₁ aR, fun s hs => ?_⟩
      have hs₁ : a₁ < ((s : ℂ)).re := by
        rw [Complex.ofReal_re]
        exact lt_of_le_of_lt (le_max_left _ _) hs
      have hsR : aR < ((s : ℂ)).re := by
        rw [Complex.ofReal_re]
        exact lt_of_le_of_lt (le_max_right _ _) hs
      refine ⟨hcv s hs₁, ?_⟩
      rw [(hR s hsR).2, hQ, map_zero, zero_mul, RatFunc.eval_zero]
    have hrestr := eq_zero_on_restriction_of_integrals_eq_zero h π hπ.2.1.1 ℓ v hres hzero
    have hmir := whittaker_mirabolic_eq_of_levi_eq ψ v.val 0 (fun g => by
      rw [hrestr g]
      rfl)
    obtain ⟨v', hv'⟩ := modelMap_surjective π ℓ v
    have hv'0 : v' = 0 := by
      apply hinj F (n + 1) ψ π hπ ℓ hℓ
      funext p
      have hp := hmir p
      rw [← hv'] at hp
      change ℓ.val (π p.val v') = 0 at hp
      show ℓ.val (π p.val v') = ℓ.val (π p.val 0)
      rw [hp, map_zero, map_zero]
    rw [← hv', hv'0, map_zero]
  · refine ⟨μ.real (sphericalCell h.uniformizer 0) * v.val.val 1, fun x => ?_⟩
    obtain ⟨hcv, Q, hRQ, hneg, h0, hbound⟩ := hx x
    have hQ : Q = LaurentPolynomial.C (μ.real (sphericalCell h.uniformizer 0) * v.val.val 1) := by
      apply LaurentPolynomial.ext
      intro k
      rw [LaurentPolynomial.C_apply]
      split_ifs with hk
      · rw [hk, h0]
      · by_contra hne
        have hk' := hbound k hne
        rw [hum, sub_self] at hk'
        rcases lt_or_gt_of_ne hk with hk0 | hk0
        · exact hne (hneg k hk0)
        · omega
    refine ⟨hcv, ?_⟩
    rw [hQ, laurentToRatFunc_C, ← RatFunc.smul_eq_C_mul] at hRQ
    exact hRQ

end Assembly

end Langlands.Conductor

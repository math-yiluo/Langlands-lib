import Langlands.AlgebraicGeometry.LangWeil.StepanovCountingProof
import Langlands.AlgebraicGeometry.LangWeil.StepanovNormPolynomialsStatement
import Langlands.AlgebraicGeometry.LangWeil.PlaneCurveElementaryReductionsStatement

universe u

namespace Langlands.AlgebraicGeometry.LangWeil

open scoped BigOperators

private theorem plane_count_eq_fibre_sum {F : Type u} [Field F] [Fintype F]
    (f : MvPolynomial (Fin 2) F) :
    Nat.card {v : Fin 2 → F // MvPolynomial.eval v f = 0} =
      ∑ x : F, Nat.card {y : F // MvPolynomial.eval ![x, y] f = 0} := by
  classical
  let e : {v : Fin 2 → F // MvPolynomial.eval v f = 0} ≃
      (Σ x : F, {y : F // MvPolynomial.eval ![x, y] f = 0}) :=
    { toFun := fun v => ⟨v.1 0, v.1 1, by
        have hv : ![v.1 0, v.1 1] = v.1 := by
          funext i
          fin_cases i <;> rfl
        simpa only [hv] using v.2⟩
      invFun := fun v => ⟨![v.1, v.2.1], v.2.2⟩
      left_inv := by
        intro v
        apply Subtype.ext
        funext i
        fin_cases i <;> rfl
      right_inv := by
        rintro ⟨x, y, hy⟩
        rfl }
  rw [Nat.card_congr e, Nat.card_sigma]

private theorem threshold_sqrt (m n q : ℕ)
    (hq : 9 * (m + 1) ^ 2 * (n + 1) ^ 2 < q) :
    3 * ((m : ℝ) + 1) * (n + 1) < Real.sqrt q := by
  have hqR : (9 : ℝ) * (m + 1) ^ 2 * (n + 1) ^ 2 < q := by
    exact_mod_cast hq
  have hs0 := Real.sqrt_nonneg (q : ℝ)
  have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ q by positivity)
  nlinarith [sq_nonneg (3 * ((m : ℝ) + 1) * (n + 1) + Real.sqrt q)]

private theorem separable_plane_curve_count
    (hNorm : StepanovNormPolynomialsStatement.{u})
    (F : Type u) [Field F] [Finite F] (f : MvPolynomial (Fin 2) F)
    (hirr : Irreducible (MvPolynomial.map (algebraMap F (AlgebraicClosure F)) f))
    (hdx : MvPolynomial.pderiv 0 f ≠ 0) (hdy : MvPolynomial.pderiv 1 f ≠ 0)
    (hn : 2 ≤ f.degreeOf 1) (hnm : f.degreeOf 1 ≤ f.degreeOf 0)
    (hq : 9 * (f.degreeOf 0 + 1) ^ 2 * (f.degreeOf 1 + 1) ^ 2 < Nat.card F) :
    |(Nat.card {v : Fin 2 → F // MvPolynomial.eval v f = 0} : ℝ) - (Nat.card F : ℝ)| <
      2 * (f.degreeOf 0 * f.degreeOf 1 ^ 2 : ℕ) * Real.sqrt (Nat.card F) := by
  classical
  let _ := Fintype.ofFinite F
  let r := fun x : F => Nat.card {y : F // MvPolynomial.eval ![x, y] f = 0}
  have hc := stepanovCounting F r (f.degreeOf 0) (f.degreeOf 1) hn hnm
    (by simpa only [Nat.card_eq_fintype_card] using hq) (by
      intro M hM hcore hMn
      obtain ⟨s, h₁, h₂, hs, hr, _hh₁, _hh₂, hd₁, hd₂, hmult⟩ :=
        hNorm F f hirr hdx hdy hn hnm M hM
          (by simpa only [Nat.card_eq_fintype_card] using hcore)
          (by simpa only [Nat.card_eq_fintype_card] using hMn)
      exact ⟨s, h₁, h₂,
        by simpa only [Nat.card_eq_fintype_card] using hs, hr,
        by simpa only [Nat.card_eq_fintype_card] using hd₁,
        by simpa only [Nat.card_eq_fintype_card] using hd₂, hmult⟩)
  simpa only [plane_count_eq_fibre_sum f, r, Nat.card_eq_fintype_card] using hc

private theorem sorted_degree_bounds (a b m n : ℕ)
    (hm : m ≤ max a b) (hn : n ≤ min a b) :
    9 * (m + 1) ^ 2 * (n + 1) ^ 2 ≤ 9 * (a + 1) ^ 2 * (b + 1) ^ 2 ∧
      m * n ^ 2 ≤ min (a ^ 2 * b) (b ^ 2 * a) := by
  rcases le_total a b with hab | hba
  · simp only [max_eq_right hab, min_eq_left hab] at hm hn
    constructor
    · calc
        9 * (m + 1) ^ 2 * (n + 1) ^ 2 ≤ 9 * (b + 1) ^ 2 * (a + 1) ^ 2 := by
          gcongr
        _ = _ := by ring
    · have h := Nat.mul_le_mul hm (Nat.pow_le_pow_left hn 2)
      have horder : b * a ^ 2 ≤ b ^ 2 * a := by
        nlinarith [Nat.mul_le_mul_right (a * b) hab]
      exact le_min (by nlinarith) (h.trans horder)
  · simp only [max_eq_left hba, min_eq_right hba] at hm hn
    constructor
    · gcongr
    · have h := Nat.mul_le_mul hm (Nat.pow_le_pow_left hn 2)
      have horder : a * b ^ 2 ≤ a ^ 2 * b := by
        nlinarith [Nat.mul_le_mul_right (a * b) hba]
      exact le_min (h.trans horder) (by nlinarith)

/-- The exact published plane-curve estimate follows from the auxiliary polynomial
construction and the elementary coordinate reductions. This is a conditional reduction;
both of its mathematical inputs still require independent proofs. -/
theorem planeCurveHasseWeil_of_stepanov
    (hNorm : StepanovNormPolynomialsStatement.{u})
    (hRed : PlaneCurveElementaryReductionsStatement.{u}) :
    PlaneCurveHasseWeilStatement.{u} := by
  intro F _ _ f hirr hm hn hq
  obtain ⟨g, hgirr, hgdx, hgdy, hgn, hgnm, hgm, hgn', hcount⟩ :=
    hRed.1 F f hirr hm hn
  obtain ⟨hthreshold, hcoeff⟩ :=
    sorted_degree_bounds (f.degreeOf 0) (f.degreeOf 1)
      (g.degreeOf 0) (g.degreeOf 1) hgm hgn'
  have hgq := hthreshold.trans_lt hq
  have hg :
      |(Nat.card {v : Fin 2 → F // MvPolynomial.eval v g = 0} : ℝ) - (Nat.card F : ℝ)| <
        2 * (g.degreeOf 0 * g.degreeOf 1 ^ 2 : ℕ) * Real.sqrt (Nat.card F) := by
    by_cases hg1 : g.degreeOf 1 = 1
    · have hl := hRed.2 F g hgirr hg1
      have hs := threshold_sqrt (g.degreeOf 0) (g.degreeOf 1) (Nat.card F) hgq
      have hmR : (0 : ℝ) < g.degreeOf 0 := by exact_mod_cast hgn.trans_le hgnm
      have hs1 : (1 : ℝ) < Real.sqrt (Nat.card F) := by
        rw [hg1] at hs
        norm_num at hs
        nlinarith
      simp only [hg1, one_pow, mul_one]
      nlinarith [mul_pos hmR (sub_pos.mpr hs1)]
    · exact separable_plane_curve_count hNorm F g hgirr hgdx hgdy (by omega) hgnm hgq
  rw [hcount] at hg
  refine hg.trans_le ?_
  have hcoeffR : ((g.degreeOf 0 * g.degreeOf 1 ^ 2 : ℕ) : ℝ) ≤
      (min (f.degreeOf 0 ^ 2 * f.degreeOf 1) (f.degreeOf 1 ^ 2 * f.degreeOf 0) : ℕ) := by
    exact_mod_cast hcoeff
  gcongr

end Langlands.AlgebraicGeometry.LangWeil

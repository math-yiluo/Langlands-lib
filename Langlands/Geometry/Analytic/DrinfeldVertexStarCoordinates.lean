import Langlands.Geometry.Analytic.DrinfeldSortedWeights
import Langlands.Geometry.Analytic.DrinfeldSortedStar

/-! # Coordinates of the vertex star and its thickening -/

noncomputable section

universe v w u

namespace Langlands.Analytic

open scoped ENNReal

namespace VectorNorm

variable {F : Type v} [NormedField F] {V : Type w} [AddCommGroup V] [Module F V]

/-- The natural logarithms of the weights of a vector norm in a basis. -/
def logBasisWeights {ι : Type u} (ν : VectorNorm F V) (b : Module.Basis ι F V) (i : ι) : ℝ :=
  Real.log (ν (b i))

theorem logBasisWeights_mono {ι : Type u} [Preorder ι] {ν : VectorNorm F V}
    {b : Module.Basis ι F V} (h : Monotone fun i => ν (b i)) : Monotone (ν.logBasisWeights b) :=
  fun i _ hij => Real.log_le_log (ν.pos (b.ne_zero i)) (h hij)

/-- The distance from a norm to the reference norm of a normalized sorted basis is
its largest weight divided by its smallest. -/
theorem IsNormalizedBasis.distRatio_eq_of_sorted {d : ℕ} {ν μ : VectorNorm F V}
    {b : Module.Basis (Fin (d + 1)) F V} (hμ : μ.IsNormalizedBasis b)
    (hν : ν.IsAdaptedBasis b) (hw : Monotone fun i => ν (b i)) :
    distRatio ν μ = ENNReal.ofReal (ν (b (Fin.last d)) / ν (b 0)) := by
  have h₁ : ∀ i, ν (b i) / μ (b i) ≤ ν (b (Fin.last d)) / μ (b (Fin.last d)) := by
    intro i
    simp only [hμ.2, div_one]
    exact hw (Fin.le_last i)
  have h₂ : ∀ i, μ (b i) / ν (b i) ≤ μ (b 0) / ν (b 0) := by
    intro i
    simp only [hμ.2]
    exact div_le_div_of_nonneg_left zero_le_one (ν.pos (b.ne_zero 0)) (hw (Fin.zero_le i))
  rw [distRatio, hν.ratioSup_eq_of_basis_max hμ.1 h₁, hμ.1.ratioSup_eq_of_basis_max hν h₂]
  simp only [hμ.2, div_one, one_div]
  rw [← ENNReal.ofReal_mul (ν.nonneg _), div_eq_mul_inv]

/-- In these coordinates, the logarithmic distance bound is a bound on the width. -/
theorem IsNormalizedBasis.distRatio_lt_iff_log_width {d : ℕ} {ν μ : VectorNorm F V}
    {b : Module.Basis (Fin (d + 1)) F V} (hμ : μ.IsNormalizedBasis b)
    (hν : ν.IsAdaptedBasis b) (hw : Monotone fun i => ν (b i)) {q : ℝ} (hq : 0 < q) :
    distRatio ν μ < ENNReal.ofReal q ↔
      ν.logBasisWeights b (Fin.last d) - ν.logBasisWeights b 0 < Real.log q := by
  rw [hμ.distRatio_eq_of_sorted hν hw, ENNReal.ofReal_lt_ofReal_iff hq]
  calc ν (b (Fin.last d)) / ν (b 0) < q ↔
      Real.exp (ν.logBasisWeights b (Fin.last d) - ν.logBasisWeights b 0) < Real.exp (Real.log q) := by
        rw [logBasisWeights, logBasisWeights, Real.exp_sub, Real.exp_log (ν.pos (b.ne_zero _)),
          Real.exp_log (ν.pos (b.ne_zero _)), Real.exp_log hq]
    _ ↔ _ := Real.exp_lt_exp

end VectorNorm

namespace NormClass

open VectorNorm

variable {F : Type v} [NontriviallyNormedField F] {V : Type w} [AddCommGroup V] [Module F V]
  {d : ℕ} {ϖ : F} (hϖ : IsMaxBelowOne ϖ)
  {ν μ : VectorNorm F V} {b : Module.Basis (Fin (d + 1)) F V}

private theorem spread_le_cut_iff {q a a' m M : ℝ} (hq : 0 < q) (ha : 0 < a) (ha' : 0 < a')
    (hm : 0 < m) (hM : 0 < M) :
    M / m ≤ q * a / a' ↔ Real.log a' - Real.log a + (Real.log M - Real.log m) ≤ Real.log q := by
  rw [show q * a / a' = q / (a' / a) by field_simp,
    le_div_iff₀ (div_pos ha' ha)]
  have he : Real.exp (Real.log a' - Real.log a + (Real.log M - Real.log m)) = M / m * (a' / a) := by
    rw [Real.exp_add, Real.exp_sub, Real.exp_sub, Real.exp_log ha', Real.exp_log ha,
      Real.exp_log hM, Real.exp_log hm, mul_comm]
  calc M / m * (a' / a) ≤ q ↔
      Real.exp (Real.log a' - Real.log a + (Real.log M - Real.log m)) ≤
        Real.exp (Real.log q) := by rw [he, Real.exp_log hq]
    _ ↔ _ := Real.exp_le_exp

private theorem pair_le_distRatio (ν η : VectorNorm F V) (x y : V) :
    ENNReal.ofReal ((ν x / η x) * (η y / ν y)) ≤ VectorNorm.distRatio ν η := by
  rw [ENNReal.ofReal_mul (div_nonneg (ν.nonneg _) (η.nonneg _))]
  exact mul_le_mul' (le_ratioSup ν η x) (le_ratioSup η ν y)

include hϖ in
/-- In a sorted common adapted basis normalized for `μ`, and at distance below `q` from
`μ`, the star of `⟦μ⟧` is exactly the sorted log-weight region with largest gap at the
wraparound. The comparison is against all vertices, not just those supplied in the basis. -/
theorem mem_vertexStar_iff_isSortedStar (hμ : μ.IsNormalizedBasis b) (hb : ν.IsAdaptedBasis b)
    (hw : Monotone fun i => ν (b i)) (hd : VectorNorm.distRatio ν μ < ENNReal.ofReal ‖ϖ‖⁻¹) :
    (⟦ν⟧ : NormClass F V) ∈ vertexStar ⟦μ⟧ ↔
      IsSortedStar (Real.log ‖ϖ‖⁻¹) (ν.logBasisWeights b) := by
  let q := ‖ϖ‖⁻¹
  have hq : 1 < q := hϖ.one_lt_inv
  have hq0 := zero_lt_one.trans hq
  let w (i : Fin (d + 1)) := ν (b i)
  have hp (i : Fin (d + 1)) : 0 < w i := ν.pos (b.ne_zero i)
  have hD := hμ.distRatio_eq_of_sorted hb hw
  have hwidth : w (Fin.last d) / w 0 < q := by
    rw [hD] at hd
    exact (ENNReal.ofReal_lt_ofReal_iff hq0).1 hd
  have hwide (a a' : Fin (d + 1)) : w a < q * w a' := calc
    w a ≤ w (Fin.last d) := hw (Fin.le_last a)
    _ < q * w 0 := (div_lt_iff₀ (hp 0)).1 hwidth
    _ ≤ q * w a' := mul_le_mul_of_nonneg_left (hw (Fin.zero_le a')) hq0.le
  have htest (i : Fin d) := spread_le_cut_iff hq0 (hp i.castSucc) (hp i.succ)
    (hp 0) (hp (Fin.last d))
  constructor
  · intro hstar
    refine ⟨logBasisWeights_mono hw, fun i => (htest i).1 ?_⟩
    by_cases hgap : w i.castSucc < w i.succ
    swap
    · have heq : w i.succ = w i.castSucc :=
        le_antisymm (not_lt.1 hgap) (hw (Fin.castSucc_le_succ i))
      rw [heq, mul_div_cancel_right₀ _ (hp i.castSucc).ne']
      exact hwidth.le
    let s := w i.castSucc
    have hs : 0 < s := hp _
    let β := ballNorm hϖ ν hs
    have hβb := hb.ballNorm hϖ hs
    have hβ (j : Fin (d + 1)) : β (b j) = if j ≤ i.castSucc then 1 else q := by
      classical
      change up q (w j / s) = _
      split_ifs with hj
      · apply up_eq_of hq (div_pos (hp j) hs) (n := 0) <;> rw [zpow_zero]
        · exact (div_le_one hs).2 (hw hj)
        · rw [← mul_div_assoc, lt_div_iff₀ hs, one_mul]
          exact hwide _ _
      · have hj' : i.succ ≤ j := Fin.castSucc_lt_iff_succ_le.1 (lt_of_not_ge hj)
        refine (up_eq_of hq (div_pos (hp j) hs) (n := 1) ?_ ?_).trans (zpow_one _) <;>
          rw [zpow_one]
        · exact ((div_lt_iff₀ hs).2 (hwide _ _)).le
        · simpa only [mul_one] using
            (mul_lt_mul_of_pos_left ((one_lt_div hs).2 (hgap.trans_le (hw hj'))) hq0)
    have h₁ : ratioSup ν β ≤ ENNReal.ofReal s := ratioSup_le_ofReal hs.le fun a _ => by
      rw [mul_comm]
      exact (div_le_iff₀ hs).1 (div_le_ballNorm hϖ ν hs a)
    have h₂ : ratioSup β ν ≤ ENNReal.ofReal (q / w i.succ) :=
      (hβb.ratioSup_le_ofReal_iff hb (div_nonneg hq0.le (hp _).le)).2 fun j => by
        apply (div_le_iff₀ (hp j)).1
        rw [hβ]
        split_ifs with hj
        · apply (div_le_div_iff₀ (hp j) (hp i.succ)).2
          simpa only [one_mul] using (hwide i.succ j).le
        · have hj' : i.succ ≤ j := Fin.castSucc_lt_iff_succ_le.1 (lt_of_not_ge hj)
          exact div_le_div_of_nonneg_left hq0.le (hp _) (hw hj')
    have hcut : VectorNorm.distRatio ν β ≤ ENNReal.ofReal (q * s / w i.succ) := by
      calc VectorNorm.distRatio ν β ≤ ENNReal.ofReal s * ENNReal.ofReal (q / w i.succ) :=
            mul_le_mul' h₁ h₂
        _ = _ := by rw [← ENNReal.ofReal_mul hs.le]; congr 1; ring
    have hle := (hstar ⟦β⟧ ⟨β, rfl, ballNorm_isLatticeNorm hϖ ν hs⟩).trans hcut
    change VectorNorm.distRatio ν μ ≤ _ at hle
    rw [hD] at hle
    exact (ENNReal.ofReal_le_ofReal_iff (div_nonneg (mul_nonneg hq0.le hs.le) (hp _).le)).1 hle
  · intro hstar e he
    by_cases heQ : distRatio ⟦ν⟧ e < ENNReal.ofReal q
    · obtain ⟨η, rfl, hη⟩ := he
      have : Nontrivial V := ⟨⟨b 0, 0, b.ne_zero 0⟩⟩
      obtain ⟨s, hs, rfl⟩ := eq_ballNorm hϖ ν hη heQ
      let β := ballNorm hϖ ν hs
      have hpβ (j : Fin (d + 1)) : 0 < β (b j) := β.pos (b.ne_zero j)
      change VectorNorm.distRatio ν μ ≤ VectorNorm.distRatio ν β
      rw [hD]
      by_cases hstep : ∃ i : Fin d, β (b i.castSucc) < β (b i.succ)
      · obtain ⟨i, hi⟩ := hstep
        obtain ⟨t, ht⟩ := ballNorm_isLatticeNorm hϖ ν hs (b i.castSucc)
        obtain ⟨t', ht'⟩ := ballNorm_isLatticeNorm hϖ ν hs (b i.succ)
        have hlt : ‖t / t'‖ < 1 := by
          change β (b i.castSucc) = ‖t‖ at ht
          change β (b i.succ) = ‖t'‖ at ht'
          rw [norm_div, ← ht, ← ht', div_lt_one (hpβ _)]
          exact hi
        have hle := hϖ.2.2 (t / t') hlt
        change β (b i.castSucc) = ‖t‖ at ht
        change β (b i.succ) = ‖t'‖ at ht'
        rw [norm_div, ← ht, ← ht', div_le_iff₀ (hpβ _)] at hle
        have hqj : q ≤ β (b i.succ) / β (b i.castSucc) :=
          (le_div_iff₀ (hpβ _)).2 ((inv_mul_le_iff₀ hϖ.1).2 hle)
        refine (ENNReal.ofReal_le_ofReal ((htest i).2 (hstar.2 i))).trans ?_
        refine (ENNReal.ofReal_le_ofReal ?_).trans (pair_le_distRatio ν β (b i.castSucc) (b i.succ))
        calc q * w i.castSucc / w i.succ ≤ (β (b i.succ) / β (b i.castSucc)) * w i.castSucc / w i.succ :=
              div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hqj (hp _).le) (hp _).le
          _ = (w i.castSucc / β (b i.castSucc)) * (β (b i.succ) / w i.succ) := by ring
      · have hmono : Monotone fun i : Fin (d + 1) => β (b i) := fun i _ hij =>
          up_mono hq (div_pos (hp i) hs) (div_le_div_of_nonneg_right (hw hij) hs.le)
        have hanti : Antitone fun i : Fin (d + 1) => β (b i) :=
          Fin.antitone_iff_succ_le.2 fun i => not_lt.1 fun h => hstep ⟨i, h⟩
        have heq : β (b 0) = β (b (Fin.last d)) :=
          le_antisymm (hmono (Fin.zero_le _)) (hanti (Fin.zero_le _))
        refine le_trans (le_of_eq ?_) (pair_le_distRatio ν β (b (Fin.last d)) (b 0))
        change ENNReal.ofReal (w (Fin.last d) / w 0) =
          ENNReal.ofReal ((w (Fin.last d) / β (b (Fin.last d))) * (β (b 0) / w 0))
        rw [heq]
        congr 1
        field_simp [(hpβ (Fin.last d)).ne']
    · exact hd.le.trans (not_lt.1 heQ)

private theorem sortedStar_width_lt {l : ℝ} {v : Fin (d + 1) → ℝ}
    (hl : 0 < l) (hv : IsSortedStar l v) : v (Fin.last d) - v 0 < l := by
  by_contra! h
  have ha : Antitone v := Fin.antitone_iff_succ_le.2 fun i => by
    have hi := hv.2 i
    linarith
  have := ha (Fin.zero_le (Fin.last d))
  linarith

include hϖ in
/-- A norm at distance less than `q` from a lattice norm belongs to the thickened star
exactly when its sorted log weights satisfy the strict `sortedStarIneq` tests. -/
theorem mem_vertexNbhd_iff_sortedStarIneq [IsUltrametricDist F] [ProperSpace F]
    (hμL : μ.IsLatticeNorm) (hμ : μ.IsNormalizedBasis b) (hb : ν.IsAdaptedBasis b)
    (hw : Monotone fun i => ν (b i)) (hd : VectorNorm.distRatio ν μ < ENNReal.ofReal ‖ϖ‖⁻¹)
    {ε : ℝ} (hε : 0 < ε) :
    (⟦ν⟧ : NormClass F V) ∈ vertexNbhd ⟦μ⟧ ε ↔
      ∀ i j, i ≤ j → sortedStarIneq (Real.log ‖ϖ‖⁻¹) ε (ν.logBasisWeights b) i j := by
  let : FiniteDimensional F V := b.finiteDimensional_of_finite
  have : Nontrivial V := ⟨⟨b 0, 0, b.ne_zero 0⟩⟩
  have hN : Module.finrank F V = d + 1 := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  have hq := inv_pos.2 hϖ.1
  have hl := Real.log_pos hϖ.one_lt_inv
  have hs := (hμ.distRatio_lt_iff_log_width hb hw hq).1 hd
  rw [← exists_isSortedStar_iff hl hε (logBasisWeights_mono hw) hs]
  constructor
  · rintro ⟨y, hy, hclose⟩
    obtain ⟨η, rfl⟩ := Quotient.exists_rep y
    have hηd : VectorNorm.distRatio η μ < ENNReal.ofReal ‖ϖ‖⁻¹ := by
      apply (distRatio_le_of_mem_vertexStar hϖ hy).trans_lt
      exact (ENNReal.ofReal_lt_ofReal_iff hq).2
        (div_lt_self hq (one_lt_gapConst hϖ (Module.finrank_pos (R := F) (M := V))))
    obtain ⟨c, hμc, hc, hwc⟩ := exists_normalized_sorted_basis_of_distRatio_lt hN hϖ hμL hηd
    refine ⟨η.logBasisWeights c, (mem_vertexStar_iff_isSortedStar hϖ hμc hc hwc hηd).1 hy, ?_⟩
    exact log_weight_diff_lt_of_distRatio_lt hb hc hμ hμc hw hwc hclose
  · rintro ⟨v, hv, hclose⟩
    let η := ofBasisWeights b (fun i => Real.exp (v i)) (fun i => Real.exp_pos (v i))
    have hc : η.IsAdaptedBasis b := isAdaptedBasis_ofBasisWeights _ _ _
    have he (i : Fin (d + 1)) : η (b i) = Real.exp (v i) := ofBasisWeights_apply_basis _ _ _ _
    have hwc : Monotone fun i => η (b i) := fun i j hij => by
      change η (b i) ≤ η (b j)
      rw [he, he]
      exact Real.exp_le_exp.2 (hv.1 hij)
    have hlogs : η.logBasisWeights b = v := funext fun i => by
      rw [logBasisWeights, he, Real.log_exp]
    have hηd : VectorNorm.distRatio η μ < ENNReal.ofReal ‖ϖ‖⁻¹ := by
      rw [hμ.distRatio_lt_iff_log_width hc hwc hq, hlogs]
      exact sortedStar_width_lt hl hv
    refine ⟨⟦η⟧, (mem_vertexStar_iff_isSortedStar hϖ hμ hc hwc hηd).2 (hlogs.symm ▸ hv), ?_⟩
    change VectorNorm.distRatio ν η < _
    refine (hb.distRatio_lt_exp_iff hc ε).2 fun i j => ?_
    simpa only [he, Real.log_exp, logBasisWeights] using hclose i j

end NormClass

end Langlands.Analytic

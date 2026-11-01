import Langlands.HarmonicAnalysis.TwoBlockRowPartialFourierSchwartz
import Langlands.HarmonicAnalysis.RowTestSmoothProof
import Langlands.HarmonicAnalysis.SchwartzBruhatValuationBoundsProof
import Langlands.Representation.RankinSelberg.TwoBlockLowerUnfoldingIntegrandData
import Langlands.Representation.Whittaker.Iwasawa

/-! Diagonal Fourier reduction and coordinate support for the lower integrand. -/

noncomputable section

open MeasureTheory Matrix
open scoped BigOperators NNReal

namespace Langlands.HarmonicAnalysis.TwoBlockRowPartialFourier

section Diagonal

variable {K : Type*} [Field K] {a b N : ℕ}

/-- The joined coordinates split right multiplication by a diagonal matrix. -/
theorem join_vecMul_diagonal (e : Fin a ⊕ Fin b ≃ Fin N) (d : Fin N → K)
    (w : Fin a → K) (v : Fin b → K) :
    (join e w v) ᵥ* diagonal d =
      join e (fun i => w i * d (e (Sum.inl i))) (fun j => v j * d (e (Sum.inr j))) := by
  funext j
  obtain ⟨s, rfl⟩ := e.surjective j
  cases s <;> simp [vecMul_diagonal]

variable [TopologicalSpace K] [IsTopologicalRing K] [MeasurableSpace K]
  [BorelSpace K] [SecondCountableTopology K]

/-- Exact supplied-measure diagonal change of variables for the partial Fourier integral. -/
theorem rowPartialFourierIntegral_diagonal
    (χ : K →*₀ ℝ≥0) (ψ : UnitaryAdditiveCharacter K) (μ : AdditiveHaarMeasure K)
    [SigmaFinite μ.measure]
    (hχ : ∀ c : K, c ≠ 0 → μ.measure.map (fun x => c * x) = (χ c)⁻¹ • μ.measure)
    (e : Fin a ⊕ Fin b ≃ Fin N) (d : Fin N → Kˣ) (f : (Fin N → K) → ℂ)
    (ξ : Fin a → K) (v : Fin b → K) :
    rowPartialFourierIntegral ψ μ e
        (fun x => f (x ᵥ* (GeneralLinear.Iwasawa.diagonalUnits d).val)) ξ v =
      (((χ (∏ i, (d (e (Sum.inl i)) : K)) : ℝ) : ℂ))⁻¹ *
        rowPartialFourierIntegral ψ μ e f
          (fun i => ξ i * (d (e (Sum.inl i)) : K)⁻¹)
          (fun j => v j * (d (e (Sum.inr j)) : K)) := by
  let g := GeneralLinear.Iwasawa.diagonalUnits (fun i => d (e (Sum.inl i)))
  let v' := fun j => v j * (d (e (Sum.inr j)) : K)
  have hj (w : Fin a → K) :
      (join e w v) ᵥ* (GeneralLinear.Iwasawa.diagonalUnits d).val =
        join e (w ᵥ* g.val) v' := by
    rw [GeneralLinear.Iwasawa.diagonalUnits_val, join_vecMul_diagonal]
    congr 1
    funext i
    simp [g, vecMul_diagonal]
  calc
    _ = rowFourierIntegral ψ μ a (fun w => f (join e (w ᵥ* g.val) v')) ξ := by
      simp only [rowPartialFourierIntegral, rowFourierIntegral, hj]
    _ = _ := by
      rw [rowFourierIntegral_vecMul χ ψ μ hχ g (fun w => f (join e w v')) ξ]
      have hginv : (g⁻¹).val = diagonal (fun i => (d (e (Sum.inl i)) : K)⁻¹) := by
        simp [g, ← map_inv]
      simp only [g, GeneralLinear.Iwasawa.diagonalUnits_val, det_diagonal, hginv,
        diagonal_transpose]
      congr 1
      congr 1
      funext i
      exact vecMul_diagonal _ _ _

end Diagonal

end Langlands.HarmonicAnalysis.TwoBlockRowPartialFourier

namespace Langlands.HarmonicAnalysis

universe uF

/-- Compact support bounds below the order of every nonzero coordinate of a row
where a Schwartz–Bruhat function is nonzero. -/
theorem exists_rowSchwartz_order_lower_bound {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) {N : ℕ}
    (Φ : letI := T.topology; SchwartzBruhat (Fin N → F.Carrier)) :
    ∃ M : ℕ, ∀ z : Fin N → F.Carrier, Φ z ≠ 0 →
      ∀ i, z i ≠ 0 → -(M : ℤ) ≤ T.ord (z i) := by
  let := T.topology
  have hq : (1 : ℝ) < T.residueCardinality := by
    exact_mod_cast T.residueCardinality_gt_one
  have hi (i : Fin N) : ∃ n : ℕ, ∀ z : Fin N → F.Carrier,
      Φ z ≠ 0 → z i ≠ 0 → -(n : ℤ) ≤ T.ord (z i) := by
    obtain ⟨B, hB⟩ := Φ.hasCompactSupport.exists_bound_of_continuousOn
      (T.continuous_normalizedAbs.comp (continuous_apply i)).continuousOn
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt B hq
    refine ⟨n, fun z hz hzi => ?_⟩
    have h1 := hB _ (subset_tsupport _ hz)
    dsimp only [Function.comp_apply] at h1
    rw [Real.norm_of_nonneg (T.normalizedAbs_nonneg _),
      T.normalizedAbs_of_ne_zero hzi] at h1
    by_contra hlt
    have h2 : (T.residueCardinality : ℝ) ^ (n : ℤ) ≤
        (T.residueCardinality : ℝ) ^ (-T.ord (z i)) :=
      zpow_le_zpow_right₀ hq.le (by omega)
    rw [zpow_natCast] at h2
    linarith
  choose ns hns using hi
  refine ⟨∑ i, ns i, fun z hz i hzi => ?_⟩
  have hle : ns i ≤ ∑ j, ns j := Finset.single_le_sum (fun j _ => Nat.zero_le (ns j))
    (Finset.mem_univ i)
  have h := hns i z hz hzi
  exact le_trans (by exact_mod_cast neg_le_neg (Int.ofNat_le.mpr hle)) h

end Langlands.HarmonicAnalysis

namespace Langlands.PadicField.TopologicalData

universe uF

/-- The inverse absolute value of a finite product of units has at most
exponential growth in the sum of their absolute orders. -/
theorem normalizedAbs_prod_inv_le_order_size {p : ℕ} [Fact p.Prime]
    {F : PadicField.{uF} p} (T : F.TopologicalData) {ι : Type*} [Fintype ι]
    (d : ι → F.Carrierˣ) :
    (T.normalizedAbs (∏ i, (d i : F.Carrier)))⁻¹ ≤
      (T.residueCardinality : ℝ) ^ (∑ i, (T.ord (d i : F.Carrier)).natAbs) := by
  classical
  have hq : (1 : ℝ) < T.residueCardinality := by
    exact_mod_cast T.residueCardinality_gt_one
  have hprod : T.normalizedAbs (∏ i, (d i : F.Carrier)) =
      ∏ i, T.normalizedAbs (d i : F.Carrier) := by
    change (T.normalizedAbsHom (∏ i, (d i : F.Carrier)) : ℝ) = _
    rw [map_prod, NNReal.coe_prod]
    rfl
  rw [hprod, ← Finset.prod_inv_distrib]
  calc
    _ ≤ ∏ i, (T.residueCardinality : ℝ) ^ (T.ord (d i : F.Carrier)).natAbs := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact inv_nonneg.mpr (T.normalizedAbs_nonneg _)
      · intro i _
        rw [T.normalizedAbs_of_ne_zero (d i).ne_zero, ← zpow_neg, neg_neg,
          ← zpow_natCast]
        exact zpow_le_zpow_right₀ hq.le Int.le_natAbs
    _ = _ := Finset.prod_pow_eq_pow_sum _ _ _

end Langlands.PadicField.TopologicalData

namespace Langlands.RankinSelberg.TwoBlockLowerUnfolding

open GeneralLinear HarmonicAnalysis HarmonicAnalysis.TwoBlockRowPartialFourier

universe uF

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
variable [MeasurableSpace F.Carrier]
  [@BorelSpace F.Carrier F.canonicalTopologicalData.topology _]
variable (ψ : letI := F.canonicalTopologicalData.topology
  UnitaryAdditiveCharacter F.Carrier)
variable (μ : letI := F.canonicalTopologicalData.topology; AdditiveHaarMeasure F.Carrier)
variable (Φ : letI := F.canonicalTopologicalData.topology
  SchwartzBruhat (Fin (t + 1) → F.Carrier))

/-- Exact diagonal formula for the actual lower partial Fourier factor. -/
theorem partialSection_diagonal (d : Fin (t + 1) → F.Carrierˣ) :
    partialSection h ψ μ Φ (Iwasawa.diagonalUnits d) =
      (F.canonicalTopologicalData.normalizedAbs
        (∏ i : Fin (m 0 + 1), (d ((succBlockShape m h).index 0 i) : F.Carrier)) : ℂ)⁻¹ *
      (letI := F.canonicalTopologicalData.topology
       rowPartialFourierIntegral ψ μ (succBlockEquiv h) Φ
        (fun i => zeta (m 0) i * (d ((succBlockShape m h).index 0 i) : F.Carrier)⁻¹)
        (fun j => eta (m 1) j * (d ((succBlockShape m h).index 1 j) : F.Carrier))) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  have : SecondCountableTopology F.Carrier := F.canonicalTopologicalData.secondCountableTopology
  have := sigmaFinite_additiveHaarMeasure μ
  have hχ (c : F.Carrier) (hc : c ≠ 0) :
      μ.measure.map (fun x => c * x) =
        (F.canonicalTopologicalData.normalizedAbsHom c)⁻¹ • μ.measure :=
    padicScalarHaarScaling F F.canonicalTopologicalData μ.measure (Units.mk0 c hc)
  change rowPartialFourierIntegral ψ μ (succBlockEquiv h)
    (fun x => Φ (x ᵥ* (Iwasawa.diagonalUnits d).val)) (zeta (m 0)) (eta (m 1)) = _
  simpa only [succBlockEquiv_inl, succBlockEquiv_inr,
    PadicField.TopologicalData.normalizedAbsHom_coe] using
    rowPartialFourierIntegral_diagonal F.canonicalTopologicalData.normalizedAbsHom ψ μ hχ
      (succBlockEquiv h) d Φ (zeta (m 0)) (eta (m 1))

/-- Uniform row-factor bound and the two endpoint order cutoffs on diagonal matrices.
The supplied self-dual measure is retained. -/
theorem exists_partialSection_diagonal_bounds
    (hsd : letI := F.canonicalTopologicalData.topology
      letI := F.canonicalTopologicalData.valuativeRel
      letI := F.canonicalTopologicalData.localField
      letI := F.canonicalTopologicalData.fieldT2
      letI : NonarchimedeanRing F.Carrier := by
        convert! ValuativeRel.nonarchimedeanRing F.Carrier
        exact Valuation.toTopologicalSpace_eq _
      IsSelfDual ψ μ) :
    ∃ (C : ℝ) (M : ℕ), 0 < C ∧ ∀ d : Fin (t + 1) → F.Carrierˣ,
      ‖partialSection h ψ μ Φ (Iwasawa.diagonalUnits d)‖ ≤
        C * (F.canonicalTopologicalData.residueCardinality : ℝ) ^
          (∑ j, (F.canonicalTopologicalData.ord (d j : F.Carrier)).natAbs) ∧
      (partialSection h ψ μ Φ (Iwasawa.diagonalUnits d) ≠ 0 →
        F.canonicalTopologicalData.ord (d ((succBlockShape m h).index 0 0) : F.Carrier) ≤ M ∧
        -(M : ℤ) ≤ F.canonicalTopologicalData.ord
          (d ((succBlockShape m h).index 1 (Fin.last (m 1))) : F.Carrier)) := by
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have : T2Space F.Carrier := T.fieldT2
  have : TotallyDisconnectedSpace F.Carrier := by
    let : NonarchimedeanRing F.Carrier := by
      convert! ValuativeRel.nonarchimedeanRing F.Carrier
      exact Valuation.toTopologicalSpace_eq _
    infer_instance
  have := sigmaFinite_additiveHaarMeasure μ
  let Ψ := partialFourierSchwartz ψ μ hsd (succBlockEquiv h) Φ
  obtain ⟨C₀, hC₀⟩ := Ψ.continuous.bounded_above_of_compact_support Ψ.hasCompactSupport
  obtain ⟨M, hM⟩ := exists_rowSchwartz_order_lower_bound F T Ψ
  refine ⟨max C₀ 1, M, lt_max_of_lt_right one_pos, fun d => ?_⟩
  let z := join (succBlockEquiv h)
    (fun i => zeta (m 0) i * (d ((succBlockShape m h).index 0 i) : F.Carrier)⁻¹)
    (fun j => eta (m 1) j * (d ((succBlockShape m h).index 1 j) : F.Carrier))
  have heq : partialSection h ψ μ Φ (Iwasawa.diagonalUnits d) =
      (T.normalizedAbs
        (∏ i : Fin (m 0 + 1), (d ((succBlockShape m h).index 0 i) : F.Carrier)) : ℂ)⁻¹ *
        Ψ z := by
    rw [partialSection_diagonal]
    simp only [Ψ, z, partialFourierSchwartz_join]
    rfl
  have habs := T.normalizedAbs_prod_inv_le_order_size
    (fun i : Fin (m 0 + 1) => d ((succBlockShape m h).index 0 i))
  have hsize : (∑ i : Fin (m 0 + 1),
      (T.ord (d ((succBlockShape m h).index 0 i) : F.Carrier)).natAbs) ≤
      ∑ j, (T.ord (d j : F.Carrier)).natAbs := by
    rw [← Equiv.sum_comp (succBlockEquiv h) (fun j => (T.ord (d j : F.Carrier)).natAbs),
      Fintype.sum_sum_type]
    simp only [succBlockEquiv_inl, succBlockEquiv_inr]
    omega
  have hq : (1 : ℝ) ≤ T.residueCardinality := by
    exact_mod_cast (le_of_lt T.residueCardinality_gt_one)
  have hfactor : (T.normalizedAbs
      (∏ i : Fin (m 0 + 1), (d ((succBlockShape m h).index 0 i) : F.Carrier)))⁻¹ ≤
      (T.residueCardinality : ℝ) ^ (∑ j, (T.ord (d j : F.Carrier)).natAbs) :=
    habs.trans (pow_le_pow_right₀ hq hsize)
  constructor
  · rw [heq, norm_mul, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg (T.normalizedAbs_nonneg _)]
    calc
      _ ≤ (T.residueCardinality : ℝ) ^ (∑ j, (T.ord (d j : F.Carrier)).natAbs) *
          max C₀ 1 := mul_le_mul hfactor ((hC₀ z).trans (le_max_left _ _))
            (norm_nonneg _) (by positivity)
      _ = _ := mul_comm _ _
  · intro hne
    have hz : Ψ z ≠ 0 := (mul_ne_zero_iff.mp (heq ▸ hne)).2
    have hfirst : z ((succBlockShape m h).index 0 0) =
        (d ((succBlockShape m h).index 0 0) : F.Carrier)⁻¹ := by
      dsimp only [z]
      rw [join_succBlockEquiv_index_zero]
      simp [zeta]
    have hlast : z ((succBlockShape m h).index 1 (Fin.last (m 1))) =
        (d ((succBlockShape m h).index 1 (Fin.last (m 1))) : F.Carrier) := by
      dsimp only [z]
      rw [join_succBlockEquiv_index_one]
      simp [eta]
    have h0 := hM z hz ((succBlockShape m h).index 0 0)
      (by rw [hfirst]; exact inv_ne_zero (d _).ne_zero)
    have h1 := hM z hz ((succBlockShape m h).index 1 (Fin.last (m 1)))
      (by rw [hlast]; exact (d _).ne_zero)
    rw [hfirst, T.ord_inv] at h0
    rw [hlast] at h1
    exact ⟨by change T.ord _ ≤ (M : ℤ); omega, h1⟩

/-- A positive diagonal growth constant and a common endpoint support cutoff
for the actual supplied partial Fourier section. -/
structure DiagonalBoundData where
  constant : ℝ
  cutoff : ℕ
  constant_pos : 0 < constant
  bounds : ∀ d : Fin (t + 1) → F.Carrierˣ,
    ‖partialSection h ψ μ Φ (Iwasawa.diagonalUnits d)‖ ≤
      constant * (F.canonicalTopologicalData.residueCardinality : ℝ) ^
        (∑ j, (F.canonicalTopologicalData.ord (d j : F.Carrier)).natAbs) ∧
    (partialSection h ψ μ Φ (Iwasawa.diagonalUnits d) ≠ 0 →
      F.canonicalTopologicalData.ord
        (d ((succBlockShape m h).index 0 0) : F.Carrier) ≤ cutoff ∧
      -(cutoff : ℤ) ≤ F.canonicalTopologicalData.ord
        (d ((succBlockShape m h).index 1 (Fin.last (m 1))) : F.Carrier))

/-- Chosen diagonal bounds, justified by self-dual partial Fourier closure. -/
def diagonalBoundData
    (hsd : letI := F.canonicalTopologicalData.topology
      letI := F.canonicalTopologicalData.valuativeRel
      letI := F.canonicalTopologicalData.localField
      letI := F.canonicalTopologicalData.fieldT2
      letI : NonarchimedeanRing F.Carrier := by
        convert! ValuativeRel.nonarchimedeanRing F.Carrier
        exact Valuation.toTopologicalSpace_eq _
      IsSelfDual ψ μ) :
    DiagonalBoundData h ψ μ Φ := by
  classical
  let hex := exists_partialSection_diagonal_bounds h ψ μ Φ hsd
  exact ⟨hex.choose, hex.choose_spec.choose,
    hex.choose_spec.choose_spec.1, hex.choose_spec.choose_spec.2⟩

end Langlands.RankinSelberg.TwoBlockLowerUnfolding

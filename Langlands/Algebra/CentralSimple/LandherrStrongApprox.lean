import Langlands.Global.Hecke.AdelicLattice
import Langlands.Global.ArchimedeanFundamentalSet
import Langlands.HarmonicAnalysis.Conductor

/-! # Strong approximation for a number field away from one finite place -/

noncomputable section

namespace Langlands.CentralSimple.Landherr

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum MeasureTheory
open NumberField.mixedEmbedding Langlands.Global.Hecke
open scoped NNReal ENNReal nonZeroDivisors

universe u

variable {F : Type u} [Field F] [NumberField F]

/-- **Small elements with denominators at one place.** For every finite divisor `m₀`, finite
place `v₀` and `δ > 0` there is a nonzero `θ ∈ F` with `v(θ) ≤ exp (m₀ v)` at every finite
`v ≠ v₀` and `w(θ) < δ` at every infinite place `w`: apply Minkowski's convex body theorem to the
fractional ideal of the divisor `m₀ + k v₀` for `k` large. -/
theorem exists_small_mem_latticeIdeal (m₀ : HeightOneSpectrum (𝓞 F) →₀ ℤ) (v₀ : HeightOneSpectrum (𝓞 F))
    (δ : ℝ≥0) (hδ : 0 < δ) :
    ∃ θ : F, θ ≠ 0 ∧ (∀ v : HeightOneSpectrum (𝓞 F), v ≠ v₀ → v.valuation F θ ≤ WithZero.exp (m₀ v)) ∧
      ∀ w : NumberField.InfinitePlace F, w θ < δ := by
  classical
  set N : ℝ := (Ideal.absNorm v₀.asIdeal : ℝ) with hN
  have hN1 : 1 < N := by
    have h0 : Ideal.absNorm v₀.asIdeal ≠ 0 :=
      Ideal.absNorm_ne_zero_iff_mem_nonZeroDivisors.mpr (mem_nonZeroDivisors_of_ne_zero v₀.ne_bot)
    have h1 : Ideal.absNorm v₀.asIdeal ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]
      exact v₀.isPrime.ne_top
    rw [hN]
    exact_mod_cast (by omega : 1 < Ideal.absNorm v₀.asIdeal)
  set A₀ : ℝ := (FractionalIdeal.absNorm (latticeIdeal m₀ : FractionalIdeal (𝓞 F)⁰ F) : ℝ)
    with hA₀
  have hA₀0 : 0 ≤ A₀ := by rw [hA₀]; exact_mod_cast FractionalIdeal.absNorm_nonneg _
  set C : ℝ≥0∞ := volume (ZSpan.fundamentalDomain (latticeBasis F)) *
    (2 : ℝ≥0∞) ^ (Module.finrank ℝ (mixedSpace F)) with hC
  have hCtop : C ≠ ⊤ := ENNReal.mul_ne_top
    (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne
    (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
  set R : ℝ≥0 := ∏ w : NumberField.InfinitePlace F, δ ^ (NumberField.InfinitePlace.mult w) with hR
  have hR0 : 0 < (R : ℝ) := by
    rw [hR, NNReal.coe_prod]
    exact Finset.prod_pos fun w _ => by positivity
  obtain ⟨k, hk⟩ : ∃ k : ℕ, A₀ * (N⁻¹) ^ k * C.toReal < R := by
    by_cases hz : A₀ * C.toReal = 0
    · exact ⟨0, by
        rw [pow_zero, mul_one]
        calc A₀ * C.toReal = 0 := hz
          _ < R := hR0⟩
    · have hpos : 0 < A₀ * C.toReal := lt_of_le_of_ne (by positivity) (Ne.symm hz)
      obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hR0 hpos)
        (inv_lt_one_of_one_lt₀ hN1)
      refine ⟨k, ?_⟩
      calc A₀ * N⁻¹ ^ k * C.toReal = N⁻¹ ^ k * (A₀ * C.toReal) := by ring
        _ < (R / (A₀ * C.toReal)) * (A₀ * C.toReal) :=
          mul_lt_mul_of_pos_right hk hpos
        _ = R := div_mul_cancel₀ _ hz
  let m : HeightOneSpectrum (𝓞 F) →₀ ℤ := m₀ + Finsupp.single v₀ (k : ℤ)
  let I := latticeIdeal m
  have hnorm : (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 F)⁰ F) : ℝ) = A₀ * (N⁻¹) ^ k := by
    have hI : I = latticeIdeal m₀ * latticeIdeal (Finsupp.single v₀ (k : ℤ)) := by
      simp only [I, m, latticeIdeal, neg_add, ClassFieldTheory.Global.finiteDivisorFractionalIdeal_add]
    rw [hI, Units.val_mul, map_mul, Rat.cast_mul, ← hA₀, absNorm_latticeIdeal]
    by_cases hk0 : k = 0
    · subst hk0
      simp
    · rw [Finsupp.support_single _ (by exact_mod_cast hk0), Finset.prod_singleton,
        Finsupp.single_eq_same, Rat.cast_zpow, Rat.cast_natCast, zpow_neg, zpow_natCast, inv_pow]
  have hmink : minkowskiBound F I < volume (convexBodyLT F (fun _ => δ)) := by
    rw [minkowskiBound, volume_fundamentalDomain_fractionalIdealLatticeBasis, convexBodyLT_volume,
      mul_assoc, ← hC]
    calc ENNReal.ofReal (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 F)⁰ F)) * C
        = ENNReal.ofReal (A₀ * (N⁻¹) ^ k * C.toReal) := by
          rw [ENNReal.ofReal_mul (by rw [← hnorm]; exact_mod_cast FractionalIdeal.absNorm_nonneg _),
            ENNReal.ofReal_toReal hCtop, ← hnorm]
      _ < ENNReal.ofReal R := (ENNReal.ofReal_lt_ofReal_iff hR0).mpr hk
      _ = (R : ℝ≥0∞) := ENNReal.ofReal_coe_nnreal
      _ ≤ (convexBodyLTFactor F : ℝ≥0∞) * (R : ℝ≥0∞) :=
          le_mul_of_one_le_left (by simp) (by exact_mod_cast one_le_convexBodyLTFactor F)
  obtain ⟨θ, hθI, hθ0, hθw⟩ := exists_ne_zero_mem_ideal_lt F I hmink
  refine ⟨θ, hθ0, fun v hv => ?_, hθw⟩
  have := (mem_latticeIdeal_iff m θ).mp hθI v
  have hs : (Finsupp.single v₀ (k : ℤ)) v = 0 := by
    simp [Ne.symm hv]
  simpa [m, hs] using this

open Filter _root_.Topology in
/-- **Strong approximation away from one finite place.** Given neighbourhoods `U v` of points
`c v` at the finite places `v ∈ S` and neighbourhoods `W w` of points `b w` at all infinite
places, and a finite place `v₀ ∉ S`, some `x ∈ F` lies in all these neighbourhoods and is
integral at every finite place outside `S ∪ {v₀}`. -/
theorem exists_strongApprox (S : Finset (HeightOneSpectrum (𝓞 F))) (v₀ : HeightOneSpectrum (𝓞 F))
    (hv₀ : v₀ ∉ S) (c : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F)
    (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (v.adicCompletion F)) (hU : ∀ v ∈ S, U v ∈ 𝓝 (c v))
    (b : ∀ w : NumberField.InfinitePlace F, w.Completion)
    (W : ∀ w : NumberField.InfinitePlace F, Set w.Completion) (hW : ∀ w, W w ∈ 𝓝 (b w)) :
    ∃ x : F, (∀ v ∈ S, algebraMap F (v.adicCompletion F) x ∈ U v) ∧
      (∀ w, algebraMap F w.Completion x ∈ W w) ∧
      ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → v ≠ v₀ → v.valuation F x ≤ 1 := by
  classical
  -- lattice levels at the places of `S`
  have hlev : ∀ v ∈ S, ∃ n : ℤ, ∀ y : v.adicCompletion F,
      y - c v ∈ (Langlands.Global.CompletionPadic.topologicalData v).additiveLattice n → y ∈ U v := by
    intro v hv
    have hs : (fun y : v.adicCompletion F => c v + y) ⁻¹' U v ∈ 𝓝 (0 : v.adicCompletion F) :=
      (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds
        (by simpa using hU v hv)
    obtain ⟨n, hn⟩ := (Langlands.Global.CompletionPadic.topologicalData v).exists_additiveLattice_subset hs
    exact ⟨n, fun y hy => by simpa using hn hy⟩
  choose! n hn using hlev
  -- radii at the infinite places
  have hrad : ∀ w, ∃ ε : ℝ, 0 < ε ∧ Metric.ball (b w) ε ⊆ W w := fun w =>
    Metric.mem_nhds_iff.mp (hW w)
  choose ε hε hεW using hrad
  -- the finite approximation
  obtain ⟨x₁, hx₁S, hx₁⟩ := exists_approx S c n
  -- bound on the archimedean fundamental set
  have hbd : ∀ w : NumberField.InfinitePlace F, ∃ C : ℝ, 0 ≤ C ∧
      ∀ d ∈ Global.archimedeanFundamentalSet F, ‖(d : NumberField.InfiniteAdeleRing F) w‖ ≤ C := by
    intro w
    have hc : IsCompact ((fun d : NumberField.InfiniteAdeleRing F => d w) ''
        Global.archimedeanFundamentalSet F) :=
      (Global.isCompact_archimedeanFundamentalSet F).image (continuous_apply w)
    obtain ⟨C, hC⟩ := hc.isBounded.exists_norm_le
    exact ⟨max C 0, le_max_right _ _, fun d hd =>
      (hC _ ⟨d, hd, rfl⟩).trans (le_max_left _ _)⟩
  choose C hC0 hC using hbd
  -- the small element
  have hδpos : ∀ w, 0 < ε w / (C w + 1) := fun w => div_pos (hε w) (by linarith [hC0 w])
  let δ : ℝ := Finset.univ.inf' Finset.univ_nonempty fun w => ε w / (C w + 1)
  have hδ : 0 < δ := (Finset.lt_inf'_iff _).mpr fun w _ => hδpos w
  let m₀ : HeightOneSpectrum (𝓞 F) →₀ ℤ := ∑ v ∈ S, Finsupp.single v (n v)
  have hm₀ : ∀ v, v ∉ S → m₀ v = 0 := fun v hv => by
    simp only [m₀, Finsupp.coe_finsetSum, Finset.sum_apply]
    exact Finset.sum_eq_zero fun u hu => by
      rw [Finsupp.single_apply, if_neg (by rintro rfl; exact hv hu)]
  have hm₀S : ∀ v ∈ S, m₀ v = n v := fun v hv => by
    simp only [m₀, Finsupp.coe_finsetSum, Finset.sum_apply]
    rw [Finset.sum_eq_single v (fun u _ hu => by rw [Finsupp.single_apply, if_neg hu])
      (fun h => absurd hv h), Finsupp.single_eq_same]
  obtain ⟨θ, hθ0, hθv, hθw⟩ := exists_small_mem_latticeIdeal m₀ v₀ ⟨δ, hδ.le⟩ hδ
  -- the archimedean correction
  let bA : NumberField.InfiniteAdeleRing F := b
  let z : NumberField.InfiniteAdeleRing F :=
    algebraMap F _ θ⁻¹ * (bA - algebraMap F (NumberField.InfiniteAdeleRing F) x₁)
  obtain ⟨a, ha⟩ := Global.exists_sub_integer_mem_archimedeanFundamentalSet F z
  refine ⟨x₁ + θ * a, fun v hv => ?_, fun w => ?_, fun v hv hv' => ?_⟩
  · apply hn v hv
    rw [map_add, add_sub_right_comm]
    refine (Langlands.Global.CompletionPadic.topologicalData v).additiveLattice (n v) |>.add_mem (hx₁S v hv) ?_
    rw [algebraMap_mem_additiveLattice_iff, map_mul]
    calc v.valuation F θ * v.valuation F (a : F) ≤ WithZero.exp (n v) * 1 := by
          gcongr
          · rw [← hm₀S v hv]; exact hθv v (fun h => hv₀ (h ▸ hv))
          · exact v.valuation_le_one a
      _ = WithZero.exp (n v) := mul_one _
  · apply hεW w
    rw [Metric.mem_ball, dist_eq_norm]
    have hz := hC w _ ha
    have hθw' : ‖algebraMap F w.Completion θ‖ < δ := by
      rw [NumberField.InfinitePlace.Completion.algebraMap_apply,
        NumberField.InfinitePlace.Completion.norm_coe]
      exact hθw w
    have hθ0w : algebraMap F w.Completion θ ≠ 0 := (map_ne_zero _).mpr hθ0
    have hzw : (z - algebraMap F (Global.InfiniteAdeles F) (a : F)) w =
        algebraMap F w.Completion θ⁻¹ * (b w - algebraMap F w.Completion x₁) -
          algebraMap F w.Completion (a : F) := rfl
    have key : algebraMap F w.Completion (x₁ + θ * a) - b w =
        -(algebraMap F w.Completion θ * ((z - algebraMap F (Global.InfiniteAdeles F) (a : F)) w)) := by
      rw [hzw, map_inv₀, map_add, map_mul]
      field_simp
      ring
    rw [key, norm_neg, norm_mul]
    calc ‖algebraMap F w.Completion θ‖ * ‖(z - algebraMap F _ (a : F)) w‖
        ≤ δ * C w := mul_le_mul hθw'.le hz (norm_nonneg _) hδ.le
      _ ≤ ε w / (C w + 1) * C w :=
          mul_le_mul_of_nonneg_right (Finset.inf'_le _ (Finset.mem_univ w)) (hC0 w)
      _ < ε w := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith [hC0 w])]
          nlinarith [hε w, hC0 w]
  · have h1 : v.valuation F x₁ ≤ 1 := by
      have := hx₁ v hv
      rwa [algebraMap_mem_additiveLattice_iff, WithZero.exp_zero] at this
    have h2 : v.valuation F (θ * a) ≤ 1 := by
      rw [map_mul]
      calc v.valuation F θ * v.valuation F (a : F) ≤ 1 * 1 := by
            gcongr
            · have := hθv v hv'
              rwa [hm₀ v hv, WithZero.exp_zero] at this
            · exact v.valuation_le_one a
        _ = 1 := mul_one _
    exact (Valuation.map_add _ _ _).trans (max_le h1 h2)

end Langlands.CentralSimple.Landherr

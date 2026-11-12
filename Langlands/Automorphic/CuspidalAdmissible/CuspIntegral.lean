import Langlands.Automorphic.CuspidalAdmissible.CuspPointwise
import Langlands.Global.AdelesSecondCountable

/-!
# The square-integral cusp estimate

For a continuous rational-left-invariant function `φ` whose constant term along the block
`(a, b)` vanishes, with the slice hypotheses of `exists_cusp_pointwise`, and a set `R` of points
`torInf x · q` (`q` in a compact set, every across-the-block gap of `x` at most `-ℓ`):

`∫_R |φ|² dν ≤ exp(-2ℓ) B² ∑_k ∫_t |dφ_k|² dν`

for every left-invariant measure `ν` and every set `t` containing the left translates of `R` by
the archimedean block unipotents `u(V)`, `V ∈ 𝒲`. The constants `B` and the compact set `𝒲`
depend only on the block, the level and the compact set.
-/

noncomputable section

universe u

open MeasureTheory NumberField
open scoped Classical Topology ENNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.CuspidalAdmissible

/-- Monotonicity of set integrals over an arbitrary set, for measurable integrands. -/
theorem setLIntegral_mono_of_forall_mem {α : Type*} [MeasurableSpace α] {ν : Measure α}
    {R : Set α} {F H : α → ℝ≥0∞} (hF : Measurable F) (hH : Measurable H)
    (h : ∀ x ∈ R, F x ≤ H x) : ∫⁻ x in R, F x ∂ν ≤ ∫⁻ x in R, H x ∂ν := by
  refine lintegral_mono_ae ?_
  rw [ae_iff]
  change (ν.restrict R) {a | F a ≤ H a}ᶜ = 0
  rw [Measure.restrict_apply (measurableSet_le hF hH).compl]
  convert measure_empty (μ := ν)
  ext x
  simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le,
    Set.mem_empty_iff_false, iff_false, not_and]
  intro hx hxR
  exact absurd (h x hxR) (not_le.mpr hx)


/-- Averaging a bound over a probability space: if `φ g ≤ ∫ F(g, x) dμ(x)` and every slice
`x ↦ ∫_R F(·, x)` is at most `c`, then `∫_R φ ≤ c`. -/
theorem setLIntegral_le_of_average {G X : Type*} [MeasurableSpace G] [MeasurableSpace X]
    (ν : Measure G) [SFinite ν] (μ : Measure X) [IsProbabilityMeasure μ] (R : Set G)
    {F : G × X → ℝ≥0∞} (hF : Measurable F) (φ : G → ℝ≥0∞)
    (hφ : ∀ g, φ g ≤ ∫⁻ x, F (g, x) ∂μ) (c : ℝ≥0∞)
    (hc : ∀ x, ∫⁻ g in R, F (g, x) ∂ν ≤ c) : ∫⁻ g in R, φ g ∂ν ≤ c := by
  calc ∫⁻ g in R, φ g ∂ν ≤ ∫⁻ g in R, (∫⁻ x, F (g, x) ∂μ) ∂ν := lintegral_mono hφ
    _ = ∫⁻ x, (∫⁻ g in R, F (g, x) ∂ν) ∂μ :=
        lintegral_lintegral_swap (f := fun g x => F (g, x)) hF.aemeasurable
    _ ≤ ∫⁻ _x, c ∂μ := lintegral_mono hc
    _ = c := by rw [lintegral_const, measure_univ, mul_one]

/-- Integrating the squared values along a continuous family of left translates of `R` that
stay in `t`, over `σ ∈ [0, 1]`, costs at most the integrals over `t`. -/
theorem setLIntegral_translates_le {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (ν : Measure G)
    [ν.IsMulLeftInvariant] [SFinite ν] {ι : Type*} (s : Finset ι) (φ : ι → G → ℂ)
    (hφ : ∀ k, Continuous (φ k)) (u : ℝ → G) (hu : Continuous u) (R t : Set G)
    (hRt : ∀ σ ∈ Set.Icc (0 : ℝ) 1, ∀ g ∈ R, u σ * g ∈ t) :
    ∫⁻ g in R, (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∑ k ∈ s, ‖φ k (u σ * g)‖ₑ ^ 2) ∂ν ≤
      ∑ k ∈ s, ∫⁻ g in t, ‖φ k g‖ₑ ^ 2 ∂ν := by
  have hm : ∀ k, Measurable fun p : G × ℝ => ‖φ k (u p.2 * p.1)‖ₑ ^ 2 := fun k =>
    ((hφ k).comp ((hu.comp continuous_snd).mul continuous_fst)).measurable.enorm.pow_const 2
  have hm' : Measurable fun p : G × ℝ => ∑ k ∈ s, ‖φ k (u p.2 * p.1)‖ₑ ^ 2 :=
    Finset.measurable_sum _ fun k _ => hm k
  have hslice : ∀ (σ : ℝ) k, Measurable fun g : G => ‖φ k (u σ * g)‖ₑ ^ 2 := fun σ k =>
    ((hφ k).comp (continuous_const.mul continuous_id)).measurable.enorm.pow_const 2
  calc ∫⁻ g in R, (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∑ k ∈ s, ‖φ k (u σ * g)‖ₑ ^ 2) ∂ν
      = ∫⁻ σ in Set.Icc (0 : ℝ) 1, (∫⁻ g in R, ∑ k ∈ s, ‖φ k (u σ * g)‖ₑ ^ 2 ∂ν) :=
        lintegral_lintegral_swap (f := fun g σ => ∑ k ∈ s, ‖φ k (u σ * g)‖ₑ ^ 2)
          hm'.aemeasurable
    _ = ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∑ k ∈ s, (∫⁻ g in R, ‖φ k (u σ * g)‖ₑ ^ 2 ∂ν) :=
        lintegral_congr fun σ => lintegral_finsetSum _ fun k _ => hslice σ k
    _ ≤ ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∑ k ∈ s, (∫⁻ g in t, ‖φ k g‖ₑ ^ 2 ∂ν) := by
        refine setLIntegral_mono' measurableSet_Icc fun σ hσ => Finset.sum_le_sum fun k _ => ?_
        rw [(measurePreserving_mul_left ν (u σ)).setLIntegral_comp_emb
          (measurableEmbedding_mulLeft (u σ)) (fun g => ‖φ k g‖ₑ ^ 2) R]
        refine lintegral_mono_set ?_
        rintro _ ⟨g, hg, rfl⟩
        exact hRt σ hσ g hg
    _ = ∑ k ∈ s, ∫⁻ g in t, ‖φ k g‖ₑ ^ 2 ∂ν := by
        rw [setLIntegral_const, Real.volume_Icc, sub_zero, ENNReal.ofReal_one, mul_one]

end Langlands.Automorphic.CuspidalAdmissible

namespace Langlands.Global

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

open Langlands.Automorphic Langlands.Automorphic.ContinuousRationalFunctions

/-- The constant-term integrand is jointly continuous in the quotient variable and the point. -/
theorem continuous_constantTermIntegrand_uncurry {a b : ℕ} (h : a + b = n)
    (G : ContinuousRationalFunctions K n) :
    Continuous (fun p : Matrix (Fin a) (Fin b) (AdeleQuotient K) × AdelicGL K n =>
      constantTermIntegrand K n h G p.2 p.1) := by
  rw [← ((isOpenQuotientMap_matrixQuotientMap (K := K) a b).prodMap
    IsOpenQuotientMap.id).continuous_comp_iff]
  have : (fun p : Matrix (Fin a) (Fin b) (AdeleQuotient K) × AdelicGL K n =>
      constantTermIntegrand K n h G p.2 p.1) ∘ Prod.map matrixQuotientMap id =
      fun p : Matrix (Fin a) (Fin b) (Adeles K) × AdelicGL K n =>
        evaluate K n G (GeneralLinear.blockUnipotent h p.1 * p.2) :=
    funext fun p => constantTermIntegrand_mk h G p.2 p.1
  rw [this]
  exact (continuous_evaluate K n G).comp
    (((GeneralLinear.continuous_blockUnipotent h).comp continuous_fst).mul continuous_snd)

/-- **Jensen with a vanishing constant term.** -/
theorem enorm_sq_le_lintegral_constantTerm [CompactSpace (AdeleQuotient K)] {a b : ℕ}
    (h : a + b = n) (G : ContinuousRationalFunctions K n) (g : AdelicGL K n)
    (hG0 : constantTerm K n h G g = 0) :
    ‖evaluate K n G g‖ₑ ^ 2 ≤
      ∫⁻ X, ‖evaluate K n G g - constantTermIntegrand K n h G g X‖ₑ ^ 2
        ∂(matrixQuotientHaar K a b) := by
  let _ : MeasurableSpace (Matrix (Fin a) (Fin b) (AdeleQuotient K)) := borel _
  have : BorelSpace (Matrix (Fin a) (Fin b) (AdeleQuotient K)) := ⟨rfl⟩
  have hint := integrable_constantTermIntegrand h G g
  have key : evaluate K n G g =
      ∫ X, (evaluate K n G g - constantTermIntegrand K n h G g X) ∂(matrixQuotientHaar K a b) := by
    rw [MeasureTheory.integral_sub (MeasureTheory.integrable_const _) hint,
      MeasureTheory.integral_const]
    unfold constantTerm at hG0
    rw [hG0]
    simp
  have hc : Continuous fun X => evaluate K n G g - constantTermIntegrand K n h G g X :=
    continuous_const.sub (continuous_constantTermIntegrand h G g)
  calc ‖evaluate K n G g‖ₑ ^ 2 = ‖∫ X, (evaluate K n G g - constantTermIntegrand K n h G g X)
        ∂(matrixQuotientHaar K a b)‖ₑ ^ 2 := congrArg (fun z : ℂ => ‖z‖ₑ ^ 2) key
    _ ≤ (∫⁻ X, ‖evaluate K n G g - constantTermIntegrand K n h G g X‖ₑ
          ∂(matrixQuotientHaar K a b)) ^ 2 := by
        gcongr
        exact enorm_integral_le_lintegral_enorm _
    _ ≤ _ := CuspidalAdmissible.sq_lintegral_le _ hc.enorm.aemeasurable

set_option maxHeartbeats 1000000 in
open ArchimedeanGL in
/-- **Square-integral cusp estimate.** -/
theorem exists_lintegral_cusp_le [CompactSpace (AdeleQuotient K)]
    [MeasurableSpace (AdelicGL K n)] [BorelSpace (AdelicGL K n)] {a b : ℕ} (h : a + b = n)
    (L : Subgroup (FiniteAdelicGL K n)) (hL : IsOpen (L : Set (FiniteAdelicGL K n)))
    (Q : Set (AdelicGL K n)) (hQ : IsCompact Q) :
    ∃ (𝒲 : Set (Matrix (Fin a) (Fin b) (InfiniteAdeles K))) (B : ℝ), IsCompact 𝒲 ∧
      ∀ (G : ContinuousRationalFunctions K n)
        (dφ : Fin (Module.finrank ℝ (ArchimedeanMatrix K n)) → AdelicGL K n → ℂ),
        (∀ g, constantTerm K n h G g = 0) → (∀ k, Continuous (dφ k)) →
        (∀ g, ∀ ℓ ∈ L, evaluate K n G (g * AdelicGL.ofFinite K n ℓ) = evaluate K n G g) →
        (∀ y : FiniteAdelicGL K n, ∃ s : SmoothFunctions K n,
          (∀ g, s.val g = evaluate K n G (AdelicGL.ofInfinite K n g * AdelicGL.ofFinite K n y)) ∧
          ∀ k g, (smoothDifferential K n (lieDirection K n k) s).val g =
            dφ k (AdelicGL.ofInfinite K n g * AdelicGL.ofFinite K n y)) →
        ∀ (ν : Measure (AdelicGL K n)) [ν.IsMulLeftInvariant] [SFinite ν] (ℓ : ℝ), 0 ≤ ℓ →
        ∀ (R t : Set (AdelicGL K n)),
          (∀ g ∈ R, ∃ (x : Fin n → ℝ) (q : AdelicGL K n), q ∈ Q ∧
            g = AdelicGL.ofInfinite K n (torInf K n x) * q ∧
            ∀ p r, x (finSumFinEquiv.trans (finCongr h) (Sum.inr r)) -
              x (finSumFinEquiv.trans (finCongr h) (Sum.inl p)) ≤ -ℓ) →
          (∀ V ∈ 𝒲, ∀ g ∈ R,
            AdelicGL.ofInfinite K n (GeneralLinear.blockUnipotent h V) * g ∈ t) →
          ∫⁻ g in R, ‖evaluate K n G g‖ₑ ^ 2 ∂ν ≤
            ENNReal.ofReal ((Real.exp (-ℓ) * B) ^ 2) *
              ∑ k, ∫⁻ g in t, ‖dφ k g‖ₑ ^ 2 ∂ν := by
  obtain ⟨𝒲, B, h𝒲, hYW⟩ := exists_cusp_pointwise K n h L hL Q hQ
  refine ⟨𝒲, B, h𝒲, fun G dφ hG0 hdφ hlevel hslice ν _ _ ℓ hℓ R t hR hRt => ?_⟩
  set C := ENNReal.ofReal ((Real.exp (-ℓ) * B) ^ 2) with hC
  have hCtop : C ≠ ⊤ := ENNReal.ofReal_ne_top
  let _ : MeasurableSpace (Matrix (Fin a) (Fin b) (AdeleQuotient K)) := borel _
  have : BorelSpace (Matrix (Fin a) (Fin b) (AdeleQuotient K)) := ⟨rfl⟩
  have : SecondCountableTopology (AdeleQuotient K) := by
    have := adeles_secondCountableTopology K
    infer_instance
  have : SecondCountableTopology (Matrix (Fin a) (Fin b) (AdeleQuotient K)) :=
    inferInstanceAs (SecondCountableTopology (Fin a → Fin b → AdeleQuotient K))
  have : IsProbabilityMeasure (matrixQuotientHaar K a b) := inferInstance
  -- continuity of the left-translated derivatives
  have hus : ∀ Wi : Matrix (Fin a) (Fin b) (InfiniteAdeles K), Continuous fun s : ℝ =>
      AdelicGL.ofInfinite K n (GeneralLinear.blockUnipotent h
        (PositiveRealIdeles.infiniteRealEmbedding K s • Wi)) := fun Wi =>
    (map_continuous (AdelicGL.ofInfinite K n)).comp
      ((GeneralLinear.continuous_blockUnipotent h).comp
        ((PositiveRealIdeles.continuous_infiniteRealEmbedding K).smul continuous_const))
  -- the bound for one quotient variable
  have hX : ∀ X : Matrix (Fin a) (Fin b) (AdeleQuotient K),
      ∫⁻ g in R, ‖evaluate K n G g - constantTermIntegrand K n h G g X‖ₑ ^ 2 ∂ν ≤
        C * ∑ k, ∫⁻ g in t, ‖dφ k g‖ₑ ^ 2 ∂ν := by
    intro X
    obtain ⟨Wi, hWi, hbound⟩ := hYW (matrixLift X)
    set u : ℝ → AdelicGL K n := fun s => AdelicGL.ofInfinite K n (GeneralLinear.blockUnipotent h
      (PositiveRealIdeles.infiniteRealEmbedding K s • Wi)) with hu
    have hHmeas : Measurable fun g : AdelicGL K n =>
        C * ∫⁻ s in Set.Icc (0 : ℝ) 1, ∑ k, ‖dφ k (u s * g)‖ₑ ^ 2 := by
      have hm : Measurable fun p : AdelicGL K n × ℝ => ∑ k, ‖dφ k (u p.2 * p.1)‖ₑ ^ 2 :=
        Finset.measurable_sum _ fun k _ => ((hdφ k).comp (((hus Wi).comp continuous_snd).mul
          continuous_fst)).measurable.enorm.pow_const 2
      exact (hm.lintegral_prod_right' (ν := volume.restrict (Set.Icc (0 : ℝ) 1))).const_mul C
    have hFmeas : Measurable fun g : AdelicGL K n =>
        ‖evaluate K n G g - constantTermIntegrand K n h G g X‖ₑ ^ 2 :=
      ((continuous_evaluate K n G).sub ((continuous_constantTermIntegrand_uncurry K n h G).comp
        (continuous_const.prodMk continuous_id))).measurable.enorm.pow_const 2
    calc ∫⁻ g in R, ‖evaluate K n G g - constantTermIntegrand K n h G g X‖ₑ ^ 2 ∂ν
        ≤ ∫⁻ g in R, C * (∫⁻ s in Set.Icc (0 : ℝ) 1, ∑ k, ‖dφ k (u s * g)‖ₑ ^ 2) ∂ν := by
          refine CuspidalAdmissible.setLIntegral_mono_of_forall_mem hFmeas hHmeas fun g hg => ?_
          obtain ⟨x, q, hq, rfl, hgap⟩ := hR g hg
          rw [enorm_sub_rev]
          exact hbound (evaluate K n G) dφ (fun γ g => evaluate_rational K n G γ g) hlevel
            hslice x ℓ hℓ hgap q hq
      _ = C * ∫⁻ g in R, (∫⁻ s in Set.Icc (0 : ℝ) 1, ∑ k, ‖dφ k (u s * g)‖ₑ ^ 2) ∂ν :=
          lintegral_const_mul' _ _ hCtop
      _ ≤ C * ∑ k, ∫⁻ g in t, ‖dφ k g‖ₑ ^ 2 ∂ν := by
          gcongr
          exact CuspidalAdmissible.setLIntegral_translates_le ν Finset.univ dφ hdφ
            u (hus Wi) R t fun σ hσ g hg => hRt _ (hWi σ hσ) g hg
  -- Jensen, Tonelli and the uniform bound
  have hJ : Measurable fun p : AdelicGL K n × Matrix (Fin a) (Fin b) (AdeleQuotient K) =>
      ‖evaluate K n G p.1 - constantTermIntegrand K n h G p.1 p.2‖ₑ ^ 2 :=
    (((continuous_evaluate K n G).comp continuous_fst).sub
      ((continuous_constantTermIntegrand_uncurry K n h G).comp
        (continuous_snd.prodMk continuous_fst))).measurable.enorm.pow_const 2
  exact CuspidalAdmissible.setLIntegral_le_of_average ν (matrixQuotientHaar K a b) R hJ
    (fun g => ‖evaluate K n G g‖ₑ ^ 2)
    (fun g => enorm_sq_le_lintegral_constantTerm K n h G g (hG0 g)) _ hX

end Langlands.Global

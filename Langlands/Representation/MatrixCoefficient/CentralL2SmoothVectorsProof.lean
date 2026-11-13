import Langlands.Representation.MatrixCoefficient.CentralL2SmoothVectorsStatement
import Langlands.Topology.LocallyProfiniteProof

/-! # `L²(G, χ, dg*)₀` is the space of smooth vectors of its Hilbert completion

Proof of Renard 2026, IV.3.1, Remark (printed p.99 / PDF p.105), for the published model
`Induction.CentralL2` with its invariant form `Induction.centralL2Form`.
-/

noncomputable section

universe uG

open MeasureTheory Filter Topology

namespace Langlands.Renard.CompactRepresentation

namespace CentralL2SmoothVectorsProof

open Induction InvariantPositiveForm

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (χ : Subgroup.center G →* ℂˣ) (hχ : ∀ z, ‖(χ z : ℂ)‖ = 1)
  [MeasurableSpace (G ⧸ Subgroup.center G)] [BorelSpace (G ⧸ Subgroup.center G)]
  (μ : Measure (G ⧸ Subgroup.center G))

/-- The integral of the square of the descended norm, in `[0, ∞]`. -/
def sqIntegral (F : CentralFunctions χ) : ENNReal :=
  ∫⁻ q, ENNReal.ofReal (centralNorm χ hχ F q ^ 2) ∂μ

omit [MeasurableSpace (G ⧸ Subgroup.center G)] [BorelSpace (G ⧸ Subgroup.center G)] in
theorem continuous_ofReal_centralNorm_sq (F : CentralFunctions χ) :
    Continuous (fun q => ENNReal.ofReal (centralNorm χ hχ F q ^ 2)) :=
  ENNReal.continuous_ofReal.comp
    ((centralNorm_isLocallyConstant χ hχ F).continuous.pow 2)

/-- A centrally covariant smooth function whose square integral is finite lies in the
published square-integrable subspace. -/
theorem mem_centralL2Submodule_of_sqIntegral_lt_top (F : CentralFunctions χ)
    (hF : sqIntegral χ hχ μ F < ⊤) : F ∈ centralL2Submodule χ hχ μ := by
  have hmeas : AEStronglyMeasurable (centralNorm χ hχ F) μ :=
    (centralNorm_isLocallyConstant χ hχ F).continuous.aestronglyMeasurable
  rw [mem_centralL2Submodule, memLp_two_iff_integrable_sq hmeas]
  refine ⟨((centralNorm_isLocallyConstant χ hχ F).continuous.pow 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun q => sq_nonneg _)]
  exact hF

/-- The image in `G / Z(G)` of a translate `x K`. -/
def cosetImage (K : Subgroup G) (x : G) : Set (G ⧸ Subgroup.center G) :=
  (fun k : G => (QuotientGroup.mk (x * k) : G ⧸ Subgroup.center G)) '' (K : Set G)

omit [MeasurableSpace (G ⧸ Subgroup.center G)] [BorelSpace (G ⧸ Subgroup.center G)] in
theorem isOpen_cosetImage (K : OpenSubgroup G) (x : G) :
    IsOpen (cosetImage K.toSubgroup x) := by
  have h : IsOpenMap (fun k : G => (QuotientGroup.mk (x * k) : G ⧸ Subgroup.center G)) :=
    QuotientGroup.isOpenMap_coe.comp (isOpenMap_mul_left x)
  exact h _ K.isOpen

omit [MeasurableSpace (G ⧸ Subgroup.center G)] [BorelSpace (G ⧸ Subgroup.center G)] in
theorem isCompact_cosetImage (K : Subgroup G) (hK : IsCompact (K : Set G)) (x : G) :
    IsCompact (cosetImage K x) :=
  hK.image (QuotientGroup.continuous_mk.comp (continuous_const.mul continuous_id))

omit [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace (G ⧸ Subgroup.center G)] [BorelSpace (G ⧸ Subgroup.center G)] in
theorem mem_cosetImage_self (K : Subgroup G) (x : G) :
    (QuotientGroup.mk x : G ⧸ Subgroup.center G) ∈ cosetImage K x :=
  ⟨1, K.one_mem, by simp⟩

/-- The square integral of a right `K`-invariant function dominates its squared value at
`x` times the measure of the image of `x K`. -/
theorem ofReal_mul_measure_le_sqIntegral (F : CentralFunctions χ) (K : OpenSubgroup G)
    (hF : ∀ k : G, k ∈ K → ∀ x, eval _ _ F (x * k) = eval _ _ F x) (x : G) :
    ENNReal.ofReal (‖eval _ _ F x‖ ^ 2) * μ (cosetImage K.toSubgroup x) ≤
      sqIntegral χ hχ μ F := by
  rw [← lintegral_indicator_const (isOpen_cosetImage K x).measurableSet]
  apply lintegral_mono
  intro q
  by_cases hq : q ∈ cosetImage K.toSubgroup x
  · rw [Set.indicator_of_mem hq]
    obtain ⟨k, hk, rfl⟩ := hq
    simp only [centralNorm_mk]
    rw [hF k hk x]
  · rw [Set.indicator_of_notMem hq]
    exact bot_le

variable [μ.IsMulRightInvariant] [μ.IsHaarMeasure]

/-- The squared completion norm of an element is its square integral. -/
theorem ofReal_norm_toHilbert_sq (f : CentralL2 χ hχ μ) :
    ENNReal.ofReal (‖(centralL2Form χ hχ μ).toHilbert f‖ ^ 2) = sqIntegral χ hχ μ f.1 := by
  rw [norm_toHilbert, centralL2Form_inner_self, Complex.ofReal_re,
    Real.sq_sqrt (integral_nonneg fun q => sq_nonneg _)]
  exact ofReal_integral_eq_lintegral_ofReal (centralL2_norm_sq_integrable χ hχ μ f)
    (Eventually.of_forall fun q => sq_nonneg _)

/-- Pointwise bound for right `K`-invariant elements. -/
theorem norm_eval_sq_mul_le (K : OpenSubgroup G) (f : CentralL2 χ hχ μ)
    (hf : f ∈ fixedVectors (centralL2Representation χ hχ μ) K.toSubgroup) (x : G) :
    ‖eval _ _ f.1 x‖ ^ 2 * (μ (cosetImage K.toSubgroup x)).toReal ≤
      ‖(centralL2Form χ hχ μ).toHilbert f‖ ^ 2 := by
  have h := ofReal_mul_measure_le_sqIntegral χ hχ μ f.1 K
    (fun k hk y => congrArg (fun F : CentralL2 χ hχ μ => eval _ _ F.1 y) (hf ⟨k, hk⟩)) x
  rw [← ofReal_norm_toHilbert_sq] at h
  have h' := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _),
    ENNReal.toReal_ofReal (sq_nonneg _)] at h'

/-- The image of the right `K`-invariant elements is closed under limits of sequences. -/
theorem exists_toHilbert_eq_of_tendsto (K : OpenSubgroup G) (hKc : IsCompact (K : Set G))
    (f : ℕ → CentralL2 χ hχ μ)
    (hf : ∀ n, f n ∈ fixedVectors (centralL2Representation χ hχ μ) K.toSubgroup)
    (w : (centralL2Form χ hχ μ).HilbertCompletion)
    (hw : Tendsto (fun n => (centralL2Form χ hχ μ).toHilbert (f n)) atTop (𝓝 w)) :
    ∃ F : CentralL2 χ hχ μ, (centralL2Form χ hχ μ).toHilbert F = w := by
  -- Pointwise Cauchy property.
  have hpt : ∀ x, CauchySeq (fun n => eval _ _ (f n).1 x) := by
    intro x
    have hfin : μ (cosetImage K.toSubgroup x) ≠ ⊤ :=
      ((isCompact_cosetImage K.toSubgroup hKc x).measure_lt_top (μ := μ)).ne
    have hpos : 0 < (μ (cosetImage K.toSubgroup x)).toReal := ENNReal.toReal_pos
      ((isOpen_cosetImage K x).measure_pos μ ⟨_, mem_cosetImage_self _ x⟩).ne' hfin
    set m := (μ (cosetImage K.toSubgroup x)).toReal with hm
    rw [Metric.cauchySeq_iff]
    intro ε hε
    have hs : 0 < Real.sqrt m := Real.sqrt_pos.mpr hpos
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hw.cauchySeq (ε * Real.sqrt m) (by positivity)
    refine ⟨N, fun p hp q hq => ?_⟩
    have hd := hN p hp q hq
    rw [dist_eq_norm, ← map_sub] at hd
    have hbound := norm_eval_sq_mul_le χ hχ μ K (f p - f q)
      (Submodule.sub_mem _ (hf p) (hf q)) x
    change ‖eval _ _ (f p).1 x - eval _ _ (f q).1 x‖ ^ 2 * m ≤ _ at hbound
    rw [dist_eq_norm]
    have hsq : ‖(centralL2Form χ hχ μ).toHilbert (f p - f q)‖ ^ 2 < ε ^ 2 * m := by
      have := pow_lt_pow_left₀ hd (norm_nonneg _) two_ne_zero
      rwa [mul_pow, Real.sq_sqrt hpos.le] at this
    have hlt : ‖eval _ _ (f p).1 x - eval _ _ (f q).1 x‖ ^ 2 < ε ^ 2 :=
      lt_of_mul_lt_mul_right (hbound.trans_lt hsq) hpos.le
    exact lt_of_pow_lt_pow_left₀ 2 hε.le hlt
  -- The pointwise limit.
  let F₀ : G → ℂ := fun x => limUnder atTop (fun n => eval _ _ (f n).1 x)
  have hF₀ : ∀ x, Tendsto (fun n => eval _ _ (f n).1 x) atTop (𝓝 (F₀ x)) :=
    fun x => (hpt x).tendsto_limUnder
  have hcov : ∀ (z : Subgroup.center G) (x : G),
      F₀ ((z : G) * x) = characterRepresentation χ z (F₀ x) := by
    intro z x
    change F₀ ((z : G) * x) = (χ z : ℂ) * F₀ x
    apply tendsto_nhds_unique (hF₀ ((z : G) * x))
    have h : (fun n => eval _ _ (f n).1 ((z : G) * x)) =
        fun n => (χ z : ℂ) * eval _ _ (f n).1 x :=
      funext fun n => eval_covariant _ _ (f n).1 z x
    rw [h]
    exact (hF₀ x).const_mul _
  have hKinv : ∀ (k : K) (x : G), F₀ (x * (k : G)) = F₀ x := by
    intro k x
    apply tendsto_nhds_unique (hF₀ (x * (k : G)))
    have h : (fun n => eval _ _ (f n).1 (x * (k : G))) = fun n => eval _ _ (f n).1 x :=
      funext fun n =>
        congrArg (fun F : CentralL2 χ hχ μ => eval _ _ F.1 x) (hf n ⟨(k : G), k.2⟩)
    rw [h]
    exact hF₀ x
  let F : CentralFunctions χ :=
    smoothFunctionOf (Subgroup.center G) (characterRepresentation χ) F₀ hcov K hKinv
  -- Fatou's lemma.
  have hfatou : ∀ n, sqIntegral χ hχ μ ((f n).1 - F) ≤
      ENNReal.ofReal (‖(centralL2Form χ hχ μ).toHilbert (f n) - w‖ ^ 2) := by
    intro n
    have hlim : ∀ q, Tendsto
        (fun p => ENNReal.ofReal (centralNorm χ hχ ((f n).1 - (f p).1) q ^ 2)) atTop
        (𝓝 (ENNReal.ofReal (centralNorm χ hχ ((f n).1 - F) q ^ 2))) := by
      intro q
      induction q using Quotient.inductionOn with
      | h x =>
        change Tendsto
          (fun p => ENNReal.ofReal (‖eval _ _ (f n).1 x - eval _ _ (f p).1 x‖ ^ 2)) atTop
          (𝓝 (ENNReal.ofReal (‖eval _ _ (f n).1 x - F₀ x‖ ^ 2)))
        exact ENNReal.tendsto_ofReal (((tendsto_const_nhds.sub (hF₀ x)).norm).pow 2)
    have hint : Tendsto (fun p => sqIntegral χ hχ μ ((f n).1 - (f p).1)) atTop
        (𝓝 (ENNReal.ofReal (‖(centralL2Form χ hχ μ).toHilbert (f n) - w‖ ^ 2))) := by
      have h : (fun p => sqIntegral χ hχ μ ((f n).1 - (f p).1)) =
          fun p => ENNReal.ofReal (‖(centralL2Form χ hχ μ).toHilbert (f n) -
            (centralL2Form χ hχ μ).toHilbert (f p)‖ ^ 2) := by
        funext p
        rw [← map_sub, ofReal_norm_toHilbert_sq]
        rfl
      rw [h]
      exact ENNReal.tendsto_ofReal (((tendsto_const_nhds.sub hw).norm).pow 2)
    calc sqIntegral χ hχ μ ((f n).1 - F)
        = ∫⁻ q, liminf (fun p =>
            ENNReal.ofReal (centralNorm χ hχ ((f n).1 - (f p).1) q ^ 2)) atTop ∂μ := by
          unfold sqIntegral
          apply lintegral_congr
          intro q
          exact ((hlim q).liminf_eq).symm
      _ ≤ liminf (fun p => sqIntegral χ hχ μ ((f n).1 - (f p).1)) atTop :=
          lintegral_liminf_le'
            (fun p => (continuous_ofReal_centralNorm_sq χ hχ _).measurable.aemeasurable)
      _ = _ := hint.liminf_eq
  have hfin : ∀ n, sqIntegral χ hχ μ ((f n).1 - F) < ⊤ :=
    fun n => (hfatou n).trans_lt ENNReal.ofReal_lt_top
  have hFmem : F ∈ centralL2Submodule χ hχ μ := by
    have h0 := mem_centralL2Submodule_of_sqIntegral_lt_top χ hχ μ _ (hfin 0)
    have h : F = (f 0).1 - ((f 0).1 - F) := (sub_sub_cancel _ _).symm
    rw [h]
    exact Submodule.sub_mem _ (f 0).2 h0
  refine ⟨⟨F, hFmem⟩, ?_⟩
  apply tendsto_nhds_unique ?_ hw
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
    (tendsto_iff_norm_sub_tendsto_zero.mp hw)
  have h := hfatou n
  have heq : sqIntegral χ hχ μ ((f n).1 - F) =
      ENNReal.ofReal (‖(centralL2Form χ hχ μ).toHilbert (f n) -
        (centralL2Form χ hχ μ).toHilbert ⟨F, hFmem⟩‖ ^ 2) := by
    rw [← map_sub, ofReal_norm_toHilbert_sq]
    rfl
  rw [heq, ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)] at h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

/-- An average of finitely many vectors at distance `r` from `w` is within `r` of `w`. -/
theorem norm_avg_sub_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {ι : Type*}
    [Fintype ι] [Nonempty ι] (x : ι → E) (y w : E) (r : ℝ)
    (hy : y = (Fintype.card ι : ℂ)⁻¹ • ∑ i, x i) (hx : ∀ i, ‖x i - w‖ = r) :
    ‖y - w‖ ≤ r := by
  subst hy
  have hn : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hn0 : (Fintype.card ι : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hw : (Fintype.card ι : ℂ)⁻¹ • ∑ _i : ι, w = w := by
    rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, inv_smul_smul₀ hn0]
  calc ‖(Fintype.card ι : ℂ)⁻¹ • ∑ i, x i - w‖
      = ‖(Fintype.card ι : ℂ)⁻¹ • ∑ i, (x i - w)‖ := by
        rw [Finset.sum_sub_distrib, smul_sub, hw]
    _ ≤ ‖(Fintype.card ι : ℂ)⁻¹‖ * ∑ i, ‖x i - w‖ := by
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
    _ = r := by
        simp only [hx, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, norm_inv,
          Complex.norm_natCast]
        rw [inv_mul_cancel_left₀ hn]

/-- Averaging over a compact open subgroup `K`: every vector of `L²(G, χ, dg*)₀` can be
replaced by a right `K`-invariant one which is at least as close to a `K`-fixed vector of
the completion. The average is a finite one, over `K / (K ∩ L)` for an open subgroup `L`
fixing the given vector. -/
theorem exists_fixed_near (K : OpenSubgroup G) (hKc : IsCompact (K : Set G))
    (w : (centralL2Form χ hχ μ).HilbertCompletion)
    (hw : ∀ k : G, k ∈ K → (centralL2Form χ hχ μ).completedRepresentation k w = w)
    (v : CentralL2 χ hχ μ) :
    ∃ f ∈ fixedVectors (centralL2Representation χ hχ μ) K.toSubgroup,
      ‖(centralL2Form χ hχ μ).toHilbert f - w‖ ≤
        ‖(centralL2Form χ hχ μ).toHilbert v - w‖ := by
  obtain ⟨L, hL⟩ := centralL2Representation_smooth χ hχ μ v
  let K' : Subgroup G := K.toSubgroup
  let L' : Subgroup K' := L.toSubgroup.subgroupOf K'
  have : CompactSpace K' := isCompact_iff_compactSpace.mp hKc
  have : Finite (K' ⧸ L') := Subgroup.quotient_finite_of_isOpen L'
    (Subgroup.subgroupOf_isOpen K' L.toSubgroup L.isOpen)
  let _ : Fintype (K' ⧸ L') := Fintype.ofFinite _
  let φ : K' ⧸ L' → CentralL2 χ hχ μ :=
    fun c => centralL2Representation χ hχ μ ((c.out : K') : G) v
  have hφ : ∀ k : K', φ (k : K' ⧸ L') = centralL2Representation χ hχ μ (k : G) v := by
    intro k
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul L' k
    have hfix : centralL2Representation χ hχ μ ((h : K') : G) v = v :=
      hL ⟨((h : K') : G), Subgroup.mem_subgroupOf.mp h.2⟩
    change centralL2Representation χ hχ μ (((k : K' ⧸ L').out : K') : G) v = _
    rw [hh, Subgroup.coe_mul, map_mul, Module.End.mul_apply, hfix]
  have hφsmul : ∀ (k : K') (c : K' ⧸ L'),
      centralL2Representation χ hχ μ (k : G) (φ c) = φ (k • c) := by
    intro k c
    induction c using QuotientGroup.induction_on with
    | H c =>
      rw [hφ, MulAction.Quotient.smul_mk, hφ, smul_eq_mul, Subgroup.coe_mul, map_mul,
        Module.End.mul_apply]
  let f : CentralL2 χ hχ μ := (Fintype.card (K' ⧸ L') : ℂ)⁻¹ • ∑ c, φ c
  refine ⟨f, ?_, ?_⟩
  · intro k
    change centralL2Representation χ hχ μ (k : G) f = f
    simp only [f, map_smul, map_sum, hφsmul]
    congr 1
    exact Equiv.sum_comp (MulAction.toPerm k) φ
  · have hterm : ∀ c, ‖(centralL2Form χ hχ μ).toHilbert (φ c) - w‖ =
        ‖(centralL2Form χ hχ μ).toHilbert v - w‖ := by
      intro c
      induction c using QuotientGroup.induction_on with
      | H k =>
        rw [hφ k]
        have hk := hw (k : G) k.2
        rw [← completedRepresentation_toHilbert]
        conv_lhs => rw [← hk]
        rw [← map_sub, completedRepresentation_norm]
    have hf_eq : (centralL2Form χ hχ μ).toHilbert f =
        (Fintype.card (K' ⧸ L') : ℂ)⁻¹ • ∑ c, (centralL2Form χ hχ μ).toHilbert (φ c) := by
      change (centralL2Form χ hχ μ).toHilbert ((Fintype.card (K' ⧸ L') : ℂ)⁻¹ • ∑ c, φ c) = _
      rw [map_smul, map_sum]
    have : Nonempty (K' ⧸ L') := ⟨QuotientGroup.mk 1⟩
    exact norm_avg_sub_le _ _ w _ hf_eq hterm

end CentralL2SmoothVectorsProof

open CentralL2SmoothVectorsProof Induction InvariantPositiveForm in
/-- Renard IV.3.1, Remark: the smooth vectors of the Hilbert completion of
`L²(G, χ, dg*)₀` are exactly the images of elements of `L²(G, χ, dg*)₀`. -/
theorem centralL2SmoothVectors : CentralL2SmoothVectorsStatement.{uG} := by
  intro G _ _ _ _ _ _ χ hχ _ _ μ _ _ b w
  constructor
  · rintro ⟨U, hU⟩
    obtain ⟨K, hKc, hKU⟩ := ((Topology.LocallyProfiniteProof.vanDantzig G).mp
      Topology.isLocallyProfinite_of_mathlib).2 (U : Set G) U.mem_nhds_one
    have hwK : ∀ k : G, k ∈ K → (centralL2Form χ hχ μ).completedRepresentation k w = w :=
      fun k hk => hU ⟨k, hKU hk⟩
    have hclos : w ∈ closure {x | ∃ f ∈ fixedVectors (centralL2Representation χ hχ μ)
        K.toSubgroup, (centralL2Form χ hχ μ).toHilbert f = x} := by
      rw [Metric.mem_closure_iff]
      intro ε hε
      obtain ⟨v, hv⟩ := (centralL2Form χ hχ μ).denseRange_toHilbert.exists_dist_lt w hε
      obtain ⟨f, hf, hfv⟩ := exists_fixed_near χ hχ μ K hKc w hwK v
      refine ⟨(centralL2Form χ hχ μ).toHilbert f, ⟨f, hf, rfl⟩, ?_⟩
      rw [dist_comm, dist_eq_norm]
      rw [dist_comm, dist_eq_norm] at hv
      exact hfv.trans_lt hv
    obtain ⟨x, hx, hxw⟩ := mem_closure_iff_seq_limit.mp hclos
    choose f hf hfx using hx
    exact exists_toHilbert_eq_of_tendsto χ hχ μ K hKc f hf w
      (hxw.congr fun n => (hfx n).symm)
  · rintro ⟨f, rfl⟩
    obtain ⟨K, hK⟩ := centralL2Representation_smooth χ hχ μ f
    refine ⟨K, ?_⟩
    intro k
    change (centralL2Form χ hχ μ).completedRepresentation (k : G)
      ((centralL2Form χ hχ μ).toHilbert f) = (centralL2Form χ hχ μ).toHilbert f
    rw [completedRepresentation_toHilbert]
    exact congrArg (centralL2Form χ hχ μ).toHilbert (hK k)

end Langlands.Renard.CompactRepresentation

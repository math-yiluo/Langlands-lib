import Langlands.Global.LeftCosetHaarMeasure
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

/-! # Measure-theoretic unfolding lemmas for discrete left quotients -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal Pointwise

namespace Langlands.Global.RankinSelbergGlobal.Unfolding

section SumUnfolding

variable {H : Type*} [Group H] [MeasurableSpace H] [MeasurableMul H]

omit [MeasurableSpace H] [MeasurableMul H] in
/-- Translating a strict fundamental domain of `Γ` by a system of representatives of
`Λ \ Γ` gives a strict fundamental domain of `Λ`. -/
theorem existsUnique_mem_iUnion_smul {Λ Γ : Subgroup H} (hΛΓ : Λ ≤ Γ)
    {s : Set H} (hs : ∀ x, ∃! γ : Γ, (γ : H) * x ∈ s)
    {ι : Type*} (ρ : ι → H) (hρΓ : ∀ i, ρ i ∈ Γ)
    (hρ : ∀ γ ∈ Γ, ∃! i, γ * (ρ i)⁻¹ ∈ Λ) (x : H) :
    ∃! l : Λ, (l : H) * x ∈ ⋃ i, ρ i • s := by
  simp only [mem_iUnion, mem_smul_set_iff_inv_smul_mem, smul_eq_mul]
  obtain ⟨γ, hγ, -⟩ := hs x
  obtain ⟨i, hi, -⟩ := hρ ((γ : H)⁻¹) (Γ.inv_mem γ.property)
  refine ⟨⟨ρ i * γ, ?_⟩, ⟨i, ?_⟩, ?_⟩
  · have := Λ.inv_mem hi
    simpa [mul_inv_rev] using this
  · simpa [mul_assoc] using hγ
  · rintro ⟨l, hl⟩ ⟨j, hj⟩
    have hl' : (ρ j)⁻¹ * l ∈ Γ := Γ.mul_mem (Γ.inv_mem (hρΓ j)) (hΛΓ hl)
    have hγ' := (hs x).unique (y₁ := ⟨(ρ j)⁻¹ * l, hl'⟩) (y₂ := γ)
      (by simpa [mul_assoc] using hj) hγ
    have hγeq : (ρ j)⁻¹ * l = γ := congrArg Subtype.val hγ'
    -- `ρ j * (ρ i)⁻¹ ∈ Λ`
    have hji : ρ j * (ρ i)⁻¹ ∈ Λ := by
      have : ρ j * (ρ i)⁻¹ = l * ((γ : H)⁻¹ * (ρ i)⁻¹) := by
        rw [← hγeq]; group
      rw [this]
      refine Λ.mul_mem hl ?_
      simpa [mul_inv_rev] using hi
    have hjj : ρ j * (ρ j)⁻¹ ∈ Λ := by simp
    obtain ⟨k, -, hk⟩ := hρ (ρ j) (hρΓ j)
    have hij : i = j := (hk i hji).trans (hk j hjj).symm
    subst hij
    apply Subtype.ext
    change l = ρ i * γ
    rw [← hγeq]; group

omit [MeasurableSpace H] [MeasurableMul H] in
/-- The translates `ρ i • s` are pairwise disjoint. -/
theorem pairwise_disjoint_smul {Λ Γ : Subgroup H}
    {s : Set H} (hs : ∀ x, ∃! γ : Γ, (γ : H) * x ∈ s)
    {ι : Type*} (ρ : ι → H) (hρΓ : ∀ i, ρ i ∈ Γ)
    (hρ : ∀ γ ∈ Γ, ∃! i, γ * (ρ i)⁻¹ ∈ Λ) :
    Pairwise (Function.onFun Disjoint fun i => ρ i • s) := by
  intro i j hij
  rw [Function.onFun, Set.disjoint_left]
  intro y hi hj
  rw [mem_smul_set_iff_inv_smul_mem, smul_eq_mul] at hi hj
  have h := (hs y).unique (y₁ := ⟨(ρ i)⁻¹, Γ.inv_mem (hρΓ i)⟩)
    (y₂ := ⟨(ρ j)⁻¹, Γ.inv_mem (hρΓ j)⟩) hi hj
  have hij' : ρ i = ρ j := inv_injective (congrArg Subtype.val h)
  obtain ⟨k, -, hk⟩ := hρ (ρ i) (hρΓ i)
  apply hij
  have h1 : ρ i * (ρ i)⁻¹ ∈ Λ := by simp
  have h2 : ρ i * (ρ j)⁻¹ ∈ Λ := by simp [hij']
  exact (hk i h1).trans (hk j h2).symm

variable (μ : Measure H) [μ.IsMulLeftInvariant]

/-- Unfolding a sum over representatives `ρ` of `Λ \ Γ`: integrating the orbit sum over a
strict fundamental domain `s` of `Γ` gives the integral over the union of the translates
`ρ i • s`, which is a strict fundamental domain of `Λ`. -/
theorem integrableOn_tsum_and_setIntegral_eq {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {Λ Γ : Subgroup H}
    {s : Set H} (hsm : MeasurableSet s) (hs : ∀ x, ∃! γ : Γ, (γ : H) * x ∈ s)
    {ι : Type*} [Countable ι] (ρ : ι → H) (hρΓ : ∀ i, ρ i ∈ Γ)
    (hρ : ∀ γ ∈ Γ, ∃! i, γ * (ρ i)⁻¹ ∈ Λ)
    {f : H → E} (hf : IntegrableOn f (⋃ i, ρ i • s) μ) :
    IntegrableOn (fun x => ∑' i, f (ρ i * x)) s μ ∧
      ∫ x in s, ∑' i, f (ρ i * x) ∂μ = ∫ x in ⋃ i, ρ i • s, f x ∂μ := by
  have hdisj := pairwise_disjoint_smul (Λ := Λ) hs ρ hρΓ hρ
  have hmeas : ∀ i, MeasurableSet (ρ i • s) := fun i => hsm.const_smul (ρ i)
  have hmp : ∀ i, MeasurePreserving (fun x => ρ i * x) μ μ := fun i =>
    measurePreserving_mul_left μ (ρ i)
  have hemb : ∀ i, MeasurableEmbedding (fun x : H => ρ i * x) := fun i =>
    measurableEmbedding_mulLeft (ρ i)
  have hpre : ∀ i, (fun x : H => ρ i * x) ⁻¹' (ρ i • s) = s := fun i => by
    ext x
    simp [mem_smul_set_iff_inv_smul_mem]
  have hmpi : ∀ i, MeasurePreserving (fun x : H => ρ i * x) (μ.restrict s)
      (μ.restrict (ρ i • s)) := fun i => by
    simpa only [hpre i] using (hmp i).restrict_preimage_emb (hemb i) (ρ i • s)
  have hsub : ∀ i, ρ i • s ⊆ ⋃ j, ρ j • s := fun i => subset_iUnion (fun j => ρ j • s) i
  have hmeasf : ∀ i, AEStronglyMeasurable (fun x => f (ρ i * x)) (μ.restrict s) := fun i =>
    ((hf.mono_set (hsub i)).1).comp_measurePreserving (hmpi i)
  have hlint : ∀ i, ∫⁻ x in s, ‖f (ρ i * x)‖ₑ ∂μ = ∫⁻ x in ρ i • s, ‖f x‖ₑ ∂μ := fun i => by
    conv_lhs => rw [← hpre i]
    exact (hmp i).setLIntegral_comp_preimage_emb (hemb i) (fun x => ‖f x‖ₑ) (ρ i • s)
  have hsum : ∑' i, ∫⁻ x in s, ‖f (ρ i * x)‖ₑ ∂μ = ∫⁻ x in ⋃ i, ρ i • s, ‖f x‖ₑ ∂μ := by
    rw [lintegral_iUnion hmeas hdisj]
    exact tsum_congr hlint
  have hfin : ∑' i, ∫⁻ x in s, ‖f (ρ i * x)‖ₑ ∂μ ≠ ∞ := by
    rw [hsum]
    exact hf.2.ne
  have hint : ∀ i, ∫ x in s, f (ρ i * x) ∂μ = ∫ x in ρ i • s, f x ∂μ := fun i => by
    conv_lhs => rw [← hpre i]
    exact (hmp i).setIntegral_preimage_emb (hemb i) _ _
  -- a.e. summability of the norms
  have htsum_lint : ∫⁻ x in s, ∑' i, ‖f (ρ i * x)‖ₑ ∂μ ≠ ∞ := by
    rw [lintegral_tsum fun i => (hmeasf i).enorm]
    exact hfin
  have hae : ∀ᵐ x ∂μ.restrict s, ∑' i, ‖f (ρ i * x)‖ₑ < ∞ :=
    ae_lt_top' (AEMeasurable.tsum fun i => (hmeasf i).enorm) htsum_lint
  have hsummable : ∀ᵐ x ∂μ.restrict s, Summable fun i => f (ρ i * x) := by
    filter_upwards [hae] with x hx
    refine Summable.of_norm ?_
    have h1 : ∑' i, ((‖f (ρ i * x)‖₊ : ℝ≥0) : ℝ≥0∞) ≠ ∞ := by
      simpa [enorm_eq_nnnorm] using hx.ne
    have h2 := ENNReal.tsum_coe_ne_top_iff_summable.mp h1
    simpa using NNReal.summable_coe.mpr h2
  have hmeas_tsum : AEStronglyMeasurable (fun x => ∑' i, f (ρ i * x)) (μ.restrict s) := by
    refine aestronglyMeasurable_of_tendsto_ae (Filter.atTop : Filter (Finset ι))
      (f := fun (t : Finset ι) x => ∑ i ∈ t, f (ρ i * x)) (fun t => ?_) ?_
    · exact Finset.aestronglyMeasurable_fun_sum _ fun i _ => hmeasf i
    · filter_upwards [hsummable] with x hx
      exact hx.hasSum
  refine ⟨⟨hmeas_tsum, ?_⟩, ?_⟩
  · calc ∫⁻ x in s, ‖∑' i, f (ρ i * x)‖ₑ ∂μ ≤ ∫⁻ x in s, ∑' i, ‖f (ρ i * x)‖ₑ ∂μ :=
          lintegral_mono fun x => enorm_tsum_le_tsum_enorm
      _ < ∞ := htsum_lint.lt_top
  · rw [integral_tsum hmeasf hfin, integral_iUnion hmeas hdisj hf]
    exact tsum_congr hint

end SumUnfolding

section Averaging

variable {H : Type*} [Group H] [MeasurableSpace H] [MeasurableMul₂ H] [MeasurableInv H]
  {N : Subgroup H}

/-- Multiplication on a subgroup is measurable for the subspace structure. -/
instance subgroupMeasurableMul₂ : MeasurableMul₂ N :=
  ⟨((measurable_subtype_coe.comp measurable_fst).mul
    (measurable_subtype_coe.comp measurable_snd)).subtype_mk⟩

/-- Inversion on a subgroup is measurable for the subspace structure. -/
instance subgroupMeasurableInv : MeasurableInv N :=
  ⟨measurable_subtype_coe.inv.subtype_mk⟩

variable (Λ : Subgroup N)

omit [MeasurableInv H] in
/-- The slice `{m ∈ N : m x ∈ s}` of a strict fundamental domain `s` of `Λ` in `H` is a
fundamental domain of `Λ` in `N`. -/
theorem isFundamentalDomain_slice {sH : Set H} (hsHm : MeasurableSet sH)
    (hsH : ∀ x : H, ∃! l : Λ, ((l : N) : H) * x ∈ sH) (ν : Measure N) (x : H) :
    IsFundamentalDomain Λ {m : N | (m : H) * x ∈ sH} ν := by
  refine IsFundamentalDomain.mk' ?_ ?_
  · exact (hsHm.preimage (measurable_subtype_coe.mul_const x)).nullMeasurableSet
  · intro m
    obtain ⟨l, hl, hu⟩ := hsH ((m : H) * x)
    refine ⟨l, ?_, fun l' hl' => hu l' ?_⟩
    · simpa [Subgroup.smul_def, mul_assoc] using hl
    · simpa [Subgroup.smul_def, mul_assoc] using hl'

variable [Countable Λ] (μ : Measure H) [μ.IsMulLeftInvariant] [SFinite μ]
  (ν : Measure N) [ν.IsMulLeftInvariant] [ν.IsInvInvariant] [SFinite ν]

/-- Weil averaging over `Λ \ N` for nonnegative functions: if `sH` and `sN` are strict
fundamental domains of the countable group `Λ ≤ N ≤ H` in `H` and in `N`, and `f` is left
`Λ`-invariant, then averaging `f` over left translates by `sN` multiplies its integral over
`sH` by `ν sN`. -/
theorem lintegral_average {sH : Set H} (hsHm : MeasurableSet sH)
    (hsH : ∀ x : H, ∃! l : Λ, ((l : N) : H) * x ∈ sH)
    {sN : Set N} (hsNm : MeasurableSet sN) (hsN : ∀ n : N, ∃! l : Λ, (l : N) * n ∈ sN)
    {f : H → ℝ≥0∞} (hf : Measurable f)
    (hfΛ : ∀ (l : Λ) (x : H), f (((l : N) : H) * x) = f x) :
    ∫⁻ n in sN, ∫⁻ x in sH, f ((n : H) * x) ∂μ ∂ν = ν sN * ∫⁻ x in sH, f x ∂μ := by
  -- the counting function `c y = ν {n ∈ sN : n⁻¹ y ∈ sH}`
  set c : H → ℝ≥0∞ := fun y => ∫⁻ n in sN, sH.indicator 1 ((n : H)⁻¹ * y) ∂ν with hc
  have hmeas2 : Measurable (fun p : N × H => sH.indicator (1 : H → ℝ≥0∞) ((p.1 : H)⁻¹ * p.2)) :=
    (measurable_one.indicator hsHm).comp
      ((measurable_subtype_coe.comp measurable_fst).inv.mul measurable_snd)
  have hcm : Measurable c := hmeas2.lintegral_prod_left'
  -- step 1: translate the inner integral
  have h1 : ∀ n : N, ∫⁻ x in sH, f ((n : H) * x) ∂μ =
      ∫⁻ y, f y * sH.indicator 1 ((n : H)⁻¹ * y) ∂μ := by
    intro n
    rw [← lintegral_mul_left_eq_self (fun y => f y * sH.indicator 1 ((n : H)⁻¹ * y)) (n : H),
      ← lintegral_indicator hsHm]
    congr 1
    ext x
    simp only [inv_mul_cancel_left]
    by_cases hx : x ∈ sH <;> simp [hx]
  -- step 2: exchange the integrals
  have h2 : ∫⁻ n in sN, ∫⁻ x in sH, f ((n : H) * x) ∂μ ∂ν = ∫⁻ y, f y * c y ∂μ := by
    simp_rw [h1]
    rw [lintegral_lintegral_swap]
    · refine lintegral_congr fun y => ?_
      rw [hc]
      exact lintegral_const_mul _ (hmeas2.comp (measurable_id.prodMk measurable_const))
    · exact ((hf.comp measurable_snd).mul hmeas2).aemeasurable
  -- step 3: fold over `Λ`
  have hFD : IsFundamentalDomain Λ sH μ := IsFundamentalDomain.mk' hsHm.nullMeasurableSet
    (fun x => by simpa [Subgroup.smul_def] using hsH x)
  have hFDN : IsFundamentalDomain Λ sN ν := IsFundamentalDomain.mk' hsNm.nullMeasurableSet
    (fun n => by simpa [Subgroup.smul_def] using hsN n)
  have hcount : ∀ x : H, ∑' l : Λ, c (l⁻¹ • x) = ν sN := by
    intro x
    set P : Set N := {m : N | (m : H)⁻¹ * x ∈ sH} with hP
    have hPm : MeasurableSet P :=
      hsHm.preimage (measurable_subtype_coe.inv.mul_const x)
    have hcl : ∀ l : Λ, c (l⁻¹ • x) = ν (l⁻¹ • P ∩ sN) := by
      intro l
      rw [hc]
      simp only
      rw [← preimage_smul]
      have : ∀ n : N, sH.indicator (1 : H → ℝ≥0∞) ((n : H)⁻¹ * (l⁻¹ • x)) =
          ((fun n : N => l • n) ⁻¹' P).indicator 1 n := by
        intro n
        by_cases hn : ((l • n : N) : H)⁻¹ * x ∈ sH
        · have hn' : (n : H)⁻¹ * (l⁻¹ • x) ∈ sH := by
            simpa [Subgroup.smul_def, mul_inv_rev, mul_assoc] using hn
          simp [indicator_of_mem hn',
            indicator_of_mem (show n ∈ (fun n : N => l • n) ⁻¹' P from hn)]
        · have hn' : (n : H)⁻¹ * (l⁻¹ • x) ∉ sH := by
            simpa [Subgroup.smul_def, mul_inv_rev, mul_assoc] using hn
          simp [indicator_of_notMem hn',
            indicator_of_notMem (show n ∉ (fun n : N => l • n) ⁻¹' P from hn)]
      simp_rw [this]
      rw [lintegral_indicator_one (hPm.preimage (measurable_const_smul _)),
        Measure.restrict_apply (hPm.preimage (measurable_const_smul _))]
    simp_rw [hcl]
    have hre := (Equiv.inv Λ).tsum_eq (fun l : Λ => ν (l • P ∩ sN))
    simp only [Equiv.inv_apply] at hre
    rw [hre, ← hFDN.measure_eq_tsum P]
    have hPinv : P = {m : N | (m : H) * x ∈ sH}⁻¹ := by
      ext m
      simp [hP]
    rw [hPinv, Measure.measure_inv]
    exact (isFundamentalDomain_slice Λ hsHm hsH ν x).measure_eq hFDN
  rw [h2, hFD.lintegral_eq_tsum']
  have h3 : ∀ l : Λ, ∫⁻ x in sH, (fun y => f y * c y) (l⁻¹ • x) ∂μ =
      ∫⁻ x in sH, f x * c (l⁻¹ • x) ∂μ := by
    intro l
    refine lintegral_congr fun x => ?_
    simp only
    congr 1
    simpa [Subgroup.smul_def] using hfΛ l⁻¹ x
  simp_rw [h3]
  rw [← lintegral_tsum (f := fun (l : Λ) x => f x * c (l⁻¹ • x))
    (fun l => (hf.mul (hcm.comp (measurable_const_smul _))).aemeasurable)]
  simp_rw [ENNReal.tsum_mul_left, hcount]
  rw [lintegral_mul_const _ hf, mul_comm]

end Averaging

section AveragingIntegral

open Langlands.Global

variable {H : Type*} [Group H] [MeasurableSpace H] [MeasurableMul₂ H] [MeasurableInv H]
  {N : Subgroup H} (Λ : Subgroup N) [Countable Λ]
  (μ : Measure H) [μ.IsMulLeftInvariant] [SFinite μ]
  (ν : Measure N) [ν.IsMulLeftInvariant] [ν.IsInvInvariant] [SFinite ν]

/-- Weil averaging over `Λ \ N` for complex functions: for a left `Λ`-invariant measurable
`F` integrable on the strict fundamental domain `sH`, the function `(n, x) ↦ F (n x)` is
integrable on `sN × sH` and its integral there is `ν sN` times the integral of `F` on `sH`. -/
theorem integrable_and_integral_average {sH : Set H} (hsHm : MeasurableSet sH)
    (hsH : ∀ x : H, ∃! l : Λ, ((l : N) : H) * x ∈ sH)
    {sN : Set N} (hsNm : MeasurableSet sN) (hsN : ∀ n : N, ∃! l : Λ, (l : N) * n ∈ sN)
    (hνfin : ν sN ≠ ∞)
    {F : H → ℂ} (hF : Measurable F)
    (hFΛ : ∀ (l : Λ) (x : H), F (((l : N) : H) * x) = F x)
    (hint : IntegrableOn F sH μ) :
    Integrable (fun p : N × H => F ((p.1 : H) * p.2)) ((ν.restrict sN).prod (μ.restrict sH)) ∧
      ∫ p, F ((p.1 : H) * p.2) ∂((ν.restrict sN).prod (μ.restrict sH)) =
        (ν sN).toReal • ∫ x in sH, F x ∂μ := by
  set Γ : Subgroup H := Λ.map N.subtype with hΓ
  have hΓmem : ∀ γ : Γ, ∃ l : Λ, ((l : N) : H) = γ := by
    rintro ⟨γ, hγ⟩
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hγ
    exact ⟨⟨n, hn⟩, rfl⟩
  have hFΓ : ∀ (γ : Γ) (x : H), F ((γ : H) * x) = F x := by
    intro γ x
    obtain ⟨l, hl⟩ := hΓmem γ
    rw [← hl]
    exact hFΛ l x
  set Fb := LeftCosetSpace.lift Γ F hFΓ with hFb_def
  have hFb : Measurable Fb := measurable_from_quotient.mpr hF
  set Ψ : N × H → LeftCosetSpace Γ := fun p => LeftCosetSpace.mk Γ ((p.1 : H) * p.2) with hΨ_def
  have hΨ : Measurable Ψ := (LeftCosetSpace.measurable_mk Γ).comp
    ((measurable_subtype_coe.comp measurable_fst).mul measurable_snd)
  have hcomp : (fun p : N × H => F ((p.1 : H) * p.2)) = Fb ∘ Ψ := rfl
  have hmap : Measure.map Ψ ((ν.restrict sN).prod (μ.restrict sH)) =
      ν sN • Measure.map (LeftCosetSpace.mk Γ) (μ.restrict sH) := by
    ext A hA
    have hpre : MeasurableSet (LeftCosetSpace.mk Γ ⁻¹' A) := LeftCosetSpace.measurable_mk Γ hA
    rw [Measure.map_apply hΨ hA, Measure.smul_apply,
      Measure.map_apply (LeftCosetSpace.measurable_mk Γ) hA, smul_eq_mul,
      ← lintegral_indicator_one (hΨ hA),
      lintegral_prod _ ((measurable_one.indicator (hΨ hA)).aemeasurable),
      ← lintegral_indicator_one hpre]
    have hinv : ∀ (l : Λ) (x : H), (LeftCosetSpace.mk Γ ⁻¹' A).indicator (1 : H → ℝ≥0∞)
        (((l : N) : H) * x) = (LeftCosetSpace.mk Γ ⁻¹' A).indicator 1 x := by
      intro l x
      have hmk : LeftCosetSpace.mk Γ (((l : N) : H) * x) = LeftCosetSpace.mk Γ x :=
        LeftCosetSpace.mk_subgroup_mul Γ ⟨((l : N) : H), Subgroup.mem_map_of_mem _ l.2⟩ x
      have key : ∀ y : H, (LeftCosetSpace.mk Γ ⁻¹' A).indicator (1 : H → ℝ≥0∞) y =
          A.indicator 1 (LeftCosetSpace.mk Γ y) := fun y =>
        Set.indicator_comp_right (s := A) (LeftCosetSpace.mk Γ)
          (g := (1 : LeftCosetSpace Γ → ℝ≥0∞)) (x := y)
      rw [key, key, hmk]
    have := lintegral_average Λ μ ν hsHm hsH hsNm hsN
      (measurable_one.indicator hpre) hinv
    exact this
  have hFbint : Integrable Fb (Measure.map (LeftCosetSpace.mk Γ) (μ.restrict sH)) :=
    (integrable_map_measure hFb.aestronglyMeasurable
      (LeftCosetSpace.measurable_mk Γ).aemeasurable).mpr hint
  refine ⟨?_, ?_⟩
  · rw [hcomp, ← integrable_map_measure hFb.aestronglyMeasurable hΨ.aemeasurable, hmap]
    exact hFbint.smul_measure hνfin
  · show ∫ p, Fb (Ψ p) ∂((ν.restrict sN).prod (μ.restrict sH)) = _
    rw [← integral_map hΨ.aemeasurable hFb.aestronglyMeasurable, hmap,
      integral_smul_measure, integral_map (LeftCosetSpace.measurable_mk Γ).aemeasurable
        hFb.aestronglyMeasurable]
    rfl

end AveragingIntegral

section Representatives

open Langlands.Global

variable {H : Type*} [Group H] (Γ : Subgroup H)

/-- Evaluating a left `Γ`-invariant function at quotient representatives is its descent. -/
theorem out_eq_lift {E : Type*} (f : H → E)
    (hf : ∀ (γ : Γ) (x : H), f ((γ : H) * x) = f x) :
    (fun q : LeftCosetSpace Γ => f q.out) = LeftCosetSpace.lift Γ f hf := by
  funext q
  conv_rhs => rw [← Quotient.out_eq q]
  rfl

/-- The representative of the class of `x` is a left `Γ`-translate of `x`. -/
theorem exists_out_mk_eq (x : H) :
    ∃ γ : Γ, (LeftCosetSpace.mk Γ x).out = (γ : H) * x := by
  have h : LeftCosetSpace.mk Γ (LeftCosetSpace.mk Γ x).out = LeftCosetSpace.mk Γ x :=
    Quotient.out_eq _
  rw [LeftCosetSpace.mk_eq_mk_iff] at h
  refine ⟨⟨_, Γ.inv_mem h⟩, ?_⟩
  simp

variable [MeasurableSpace H]

/-- Integrability of an invariant function's descent for a quotient measure built from
a set of representatives. -/
theorem integrable_out_iff {f : H → ℂ} (hfm : Measurable f)
    (hf : ∀ (γ : Γ) (x : H), f ((γ : H) * x) = f x) (ν : Measure H) (s : Set H) :
    Integrable (fun q : LeftCosetSpace Γ => f q.out) (LeftCosetSpace.quotientMeasure Γ ν s) ↔
      IntegrableOn f s ν := by
  rw [out_eq_lift Γ f hf]
  have hm : Measurable (LeftCosetSpace.lift Γ f hf) := measurable_from_quotient.mpr hfm
  rw [LeftCosetSpace.quotientMeasure, integrable_map_measure hm.aestronglyMeasurable
    (LeftCosetSpace.measurable_mk Γ).aemeasurable]
  rfl

/-- The integral of an invariant function's descent for a quotient measure built from a
set of representatives. -/
theorem integral_out_eq {f : H → ℂ} (hfm : Measurable f)
    (hf : ∀ (γ : Γ) (x : H), f ((γ : H) * x) = f x) (ν : Measure H) (s : Set H) :
    ∫ q, f q.out ∂(LeftCosetSpace.quotientMeasure Γ ν s) = ∫ x in s, f x ∂ν := by
  have hm : Measurable (LeftCosetSpace.lift Γ f hf) := measurable_from_quotient.mpr hfm
  rw [out_eq_lift Γ f hf, LeftCosetSpace.quotientMeasure,
    integral_map (LeftCosetSpace.measurable_mk Γ).aemeasurable hm.aestronglyMeasurable]
  rfl

end Representatives

section CosetRepresentatives

variable {H : Type*} [Group H] (Λ Γ : Subgroup H)

/-- Representatives of the cosets `Λ \ Γ`, as elements of the ambient group. -/
def cosetRep (q : Quotient (QuotientGroup.rightRel (Λ.subgroupOf Γ))) : H :=
  ((q.out : Γ) : H)

theorem cosetRep_mem (q : Quotient (QuotientGroup.rightRel (Λ.subgroupOf Γ))) :
    cosetRep Λ Γ q ∈ Γ :=
  (q.out : Γ).property

/-- Every element of `Γ` lies in exactly one coset `Λ ρ(q)`. -/
theorem existsUnique_cosetRep (γ : H) (hγ : γ ∈ Γ) :
    ∃! q : Quotient (QuotientGroup.rightRel (Λ.subgroupOf Γ)),
      γ * (cosetRep Λ Γ q)⁻¹ ∈ Λ := by
  refine ⟨Quotient.mk'' ⟨γ, hγ⟩, ?_, fun q hq => ?_⟩
  · have h := Quotient.mk_out (s := QuotientGroup.rightRel (Λ.subgroupOf Γ)) ⟨γ, hγ⟩
    have h' := QuotientGroup.rightRel_apply.mp h
    have h'' : (⟨γ, hγ⟩ : Γ) * (Quotient.out
        (Quotient.mk'' ⟨γ, hγ⟩ : Quotient (QuotientGroup.rightRel (Λ.subgroupOf Γ))))⁻¹ ∈
          Λ.subgroupOf Γ := by
      exact h'
    simpa [cosetRep, Subgroup.mem_subgroupOf] using h''
  · rw [← Quotient.out_eq q]
    apply Quotient.sound
    apply QuotientGroup.rightRel_apply.mpr
    have : (⟨γ, hγ⟩ : Γ) * (q.out)⁻¹ ∈ Λ.subgroupOf Γ := by
      simpa [cosetRep, Subgroup.mem_subgroupOf] using hq
    exact this

end CosetRepresentatives

end Langlands.Global.RankinSelbergGlobal.Unfolding

import Langlands.Analysis.Local.QuotientWeilKernel
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.PartitionOfUnity
import Mathlib.Topology.UrysohnsLemma

/-!
# Normalizing functions for a closed subgroup

Let `G` be a locally compact group, `H` a closed subgroup with a right-invariant measure `μH`, and
`ν` a measure on the space `H \ G` of cosets `H g` compatible with `(μG, μH)`
(`IsCompatible H μG μH ν`). A *normalizing function* is a measurable `ρ : G → ℝ≥0∞` with
`∫⁻ h, ρ (h g) dμH(h) = 1` for every `g` (`IsNormalizingFunction`).

* `exists_continuous_isNormalizingFunction`: on a σ-compact group a continuous normalizing function
  exists whose nonvanishing points in `H · C` lie in a compact set, for every compact `C`.
* `IsCompatible.eq_map_withDensity`: `ν` is the image of `ρ · μG` in `H \ G`; hence
  `∫⁻ q, (descend F) q dν = ∫⁻ g, F g ρ g dμG` for left `H`-invariant measurable `F ≥ 0`
  (`IsCompatible.lintegral_descend_eq`), and for vector-valued `F` the descended function is
  `ν`-integrable exactly when `ρ F` is `μG`-integrable, with equal integrals
  (`IsCompatible.integrable_descend_iff`, `IsCompatible.integral_descend_eq`).

Bourbaki, *Intégration*, Chapter VII, §2, no. 3, Proposition 5, and no. 4, Propositions 8 and 9
(printed pp. 46, 51–52); Folland, *A Course in Abstract Harmonic Analysis*, §2.6.
-/

noncomputable section

namespace Langlands.QuotientIntegration

open MeasureTheory MeasureTheory.Measure Set Filter Topology
open scoped ENNReal NNReal Pointwise

universe u

private theorem quotient_mk_mul_of_mem {G : Type u} [Group G] (H : Subgroup G) (h : H) (g : G) :
    Quotient.mk (QuotientGroup.rightRel H) (h.val * g) =
      Quotient.mk (QuotientGroup.rightRel H) g := by
  apply Quotient.sound
  apply QuotientGroup.rightRel_apply.mpr
  simp [mul_inv_rev]

section Definitions

variable {G : Type u} [Group G] [MeasurableSpace G]

/-- A *normalizing function* for a subgroup `H` with measure `μH`: a measurable `ρ : G → ℝ≥0∞`
whose integral along every coset is one, `∫⁻ h, ρ (h g) ∂μH = 1` for all `g`. -/
structure IsNormalizingFunction (H : Subgroup G) [MeasurableSpace H] (μH : Measure H)
    (ρ : G → ℝ≥0∞) : Prop where
  measurable : Measurable ρ
  lintegral_eq_one : ∀ g : G, ∫⁻ h, ρ (h.val * g) ∂μH = 1

variable (H : Subgroup G) [MeasurableSpace H] [MeasurableMul H]
variable (μH : Measure H) [IsMulRightInvariant μH]

/-- The fiber integral `H g ↦ ∫⁻ h, f (h g) ∂μH` of `f : G → ℝ≥0∞`, a function on `H \ G`.
Right invariance of `μH` makes it independent of the representative. -/
def quotientAverageENNReal (f : G → ℝ≥0∞) : LeftQuotient H → ℝ≥0∞ :=
  descend H (fun g => ∫⁻ h : H, f (h.val * g) ∂μH) (fun k g => by
    simpa only [Subgroup.coe_mul, mul_assoc] using
      lintegral_mul_right_eq_self (μ := μH) (fun h : H => f (h.val * g)) k)

omit [MeasurableSpace G] in
@[simp] theorem quotientAverageENNReal_mk (f : G → ℝ≥0∞) (g : G) :
    quotientAverageENNReal H μH f (Quotient.mk _ g) = ∫⁻ h : H, f (h.val * g) ∂μH := rfl

end Definitions

/-- For the counting measure the normalizing condition is `∑' h, ρ (h g) = 1`. -/
theorem isNormalizingFunction_count_iff {G : Type u} [Group G] [MeasurableSpace G]
    (H : Subgroup G) [MeasurableSpace H] [MeasurableSingletonClass H] (ρ : G → ℝ≥0∞) :
    IsNormalizingFunction H Measure.count ρ ↔
      Measurable ρ ∧ ∀ g : G, ∑' h : H, ρ (h.val * g) = 1 := by
  simp only [← lintegral_count]
  exact ⟨fun h => ⟨h.measurable, h.lintegral_eq_one⟩, fun h => ⟨h.1, h.2⟩⟩

section Weil

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  {H : Subgroup G} [MeasurableSpace H] [BorelSpace H]
  [MeasurableSpace (LeftQuotient H)] [BorelSpace (LeftQuotient H)]
  {μG : Measure G} [IsFiniteMeasureOnCompacts μG]
  {μH : Measure H} [μH.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μH]
  {ν : Measure (LeftQuotient H)}

/-- **Weil's formula for measurable nonnegative functions**:
`∫⁻ g, f g ∂μG = ∫⁻ (H g), ∫⁻ h, f (h g) ∂μH ∂ν` for a compatible `ν`. -/
theorem IsCompatible.lintegral_eq_lintegral_quotientAverageENNReal
    (hH : IsClosed (H : Set G)) (hν : IsCompatible H μG μH ν) (f : G → ℝ≥0∞)
    (hf : Measurable f) :
    ∫⁻ g, f g ∂μG = ∫⁻ q, quotientAverageENNReal H μH f q ∂ν := by
  have := hH.locallyCompactSpace
  have : SecondCountableTopology H := TopologicalSpace.Subtype.secondCountableTopology (H : Set G)
  rw [← lintegral_orbitKernel H hH μH μG ν hν f hf]
  refine lintegral_congr fun q => ?_
  induction q using Quotient.inductionOn with
  | h g =>
    rw [orbitKernel_mk, lintegral_map hf (continuous_subtype_val.mul_const g).measurable]
    rfl

/-- A normalizing function is finite `μG`-almost everywhere. -/
theorem IsNormalizingFunction.ae_lt_top (hH : IsClosed (H : Set G))
    (hν : IsCompatible H μG μH ν) {ρ : G → ℝ≥0∞} (hρ : IsNormalizingFunction H μH ρ) :
    ∀ᵐ g ∂μG, ρ g < ⊤ := by
  have hE : MeasurableSet (ρ ⁻¹' {⊤}) := hρ.measurable (measurableSet_singleton _)
  have hset : {g | ¬ ρ g < ⊤} = ρ ⁻¹' {⊤} := by
    ext g
    simp [lt_top_iff_ne_top]
  rw [ae_iff, hset, ← lintegral_indicator_one hE,
    hν.lintegral_eq_lintegral_quotientAverageENNReal hH _ (measurable_one.indicator hE)]
  refine (lintegral_congr fun q => ?_).trans lintegral_zero
  induction q using Quotient.inductionOn with
  | h g =>
    rw [quotientAverageENNReal_mk]
    have hfin : ∀ᵐ h ∂μH, ρ (h.val * g) < ⊤ :=
      MeasureTheory.ae_lt_top
        (hρ.measurable.comp (continuous_subtype_val.mul_const g).measurable)
        (by rw [hρ.lintegral_eq_one g]; exact ENNReal.one_ne_top)
    refine (lintegral_congr_ae (hfin.mono fun h hh => ?_)).trans lintegral_zero
    simp [Set.indicator, hh.ne]

/-- **The rule for a nonnegative invariant function**: for a normalizing `ρ` and a measurable
left `H`-invariant `F ≥ 0`, `∫⁻ q, (descend F) q ∂ν = ∫⁻ g, F g * ρ g ∂μG`. -/
theorem IsCompatible.lintegral_descend_eq (hH : IsClosed (H : Set G))
    (hν : IsCompatible H μG μH ν) {ρ : G → ℝ≥0∞} (hρ : IsNormalizingFunction H μH ρ)
    (F : G → ℝ≥0∞) (hFm : Measurable F) (hF : ∀ h : H, ∀ g, F (h.val * g) = F g) :
    ∫⁻ q, descend H F hF q ∂ν = ∫⁻ g, F g * ρ g ∂μG := by
  rw [hν.lintegral_eq_lintegral_quotientAverageENNReal hH (fun g => F g * ρ g)
    (hFm.mul hρ.measurable)]
  refine lintegral_congr fun q => ?_
  induction q using Quotient.inductionOn with
  | h g =>
    rw [quotientAverageENNReal_mk, descend_mk]
    simp_rw [hF]
    have hm : Measurable fun h : H => ρ (h.val * g) :=
      hρ.measurable.comp (continuous_subtype_val.mul_const g).measurable
    rw [lintegral_const_mul _ hm, hρ.lintegral_eq_one g, mul_one]

/-- **A compatible quotient measure is the image of `ρ · μG`** for every normalizing `ρ`. -/
theorem IsCompatible.eq_map_withDensity (hH : IsClosed (H : Set G))
    (hν : IsCompatible H μG μH ν) {ρ : G → ℝ≥0∞} (hρ : IsNormalizingFunction H μH ρ) :
    ν = (μG.withDensity ρ).map (leftQuotientMap H) := by
  have hπ : Measurable (leftQuotientMap H) := continuous_quotient_mk'.measurable
  ext A hA
  rw [Measure.map_apply hπ hA, withDensity_apply _ (hπ hA), ← lintegral_indicator (hπ hA)]
  have hinv : ∀ h : H, ∀ g, A.indicator 1 (leftQuotientMap H (h.val * g)) =
      A.indicator (1 : LeftQuotient H → ℝ≥0∞) (leftQuotientMap H g) := by
    intro h g
    simp only [leftQuotientMap_apply, quotient_mk_mul_of_mem]
  have h1 := hν.lintegral_descend_eq hH hρ
    (fun g => A.indicator (1 : LeftQuotient H → ℝ≥0∞) (leftQuotientMap H g))
    ((measurable_one.indicator hA).comp hπ) hinv
  have hdesc : descend H (fun g => A.indicator (1 : LeftQuotient H → ℝ≥0∞) (leftQuotientMap H g))
      hinv = A.indicator 1 := by
    funext q
    induction q using Quotient.inductionOn with
    | h g => rfl
  rw [hdesc, lintegral_indicator_one hA] at h1
  rw [h1]
  refine lintegral_congr fun g => ?_
  by_cases hg : leftQuotientMap H g ∈ A
  · rw [indicator_of_mem hg, indicator_of_mem (show g ∈ leftQuotientMap H ⁻¹' A from hg),
      Pi.one_apply, one_mul]
  · rw [indicator_of_notMem hg, indicator_of_notMem (show g ∉ leftQuotientMap H ⁻¹' A from hg),
      zero_mul]

/-- The rule for a measurable nonnegative function `φ` on `H \ G`:
`∫⁻ q, φ q ∂ν = ∫⁻ g, φ (H g) * ρ g ∂μG`. -/
theorem IsCompatible.lintegral_eq_lintegral_mul_comp (hH : IsClosed (H : Set G))
    (hν : IsCompatible H μG μH ν) {ρ : G → ℝ≥0∞} (hρ : IsNormalizingFunction H μH ρ)
    {φ : LeftQuotient H → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ q, φ q ∂ν = ∫⁻ g, φ (leftQuotientMap H g) * ρ g ∂μG := by
  have hπ : Measurable (leftQuotientMap H) := continuous_quotient_mk'.measurable
  have hm : Measurable fun g => φ (leftQuotientMap H g) := hφ.comp hπ
  rw [hν.eq_map_withDensity hH hρ, lintegral_map hφ hπ,
    lintegral_withDensity_eq_lintegral_mul _ hρ.measurable hm]
  exact lintegral_congr fun g => mul_comm _ _

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The rule for integrability of a function `φ` on `H \ G`: `φ` is `ν`-integrable exactly when
`g ↦ ρ g • φ (H g)` is `μG`-integrable. -/
theorem IsCompatible.integrable_iff_integrable_smul_comp (hH : IsClosed (H : Set G))
    (hν : IsCompatible H μG μH ν) {ρ : G → ℝ≥0∞} (hρ : IsNormalizingFunction H μH ρ)
    {φ : LeftQuotient H → E} (hφ : AEStronglyMeasurable φ ν) :
    Integrable φ ν ↔ Integrable (fun g => (ρ g).toReal • φ (leftQuotientMap H g)) μG := by
  have hπ : Measurable (leftQuotientMap H) := continuous_quotient_mk'.measurable
  have hfin := hρ.ae_lt_top hH hν
  rw [hν.eq_map_withDensity hH hρ] at hφ ⊢
  rw [integrable_map_measure hφ hπ.aemeasurable,
    integrable_withDensity_iff_integrable_smul' hρ.measurable hfin]
  rfl

/-- The rule for the integral of a function `φ` on `H \ G`:
`∫ q, φ q ∂ν = ∫ g, ρ g • φ (H g) ∂μG`. -/
theorem IsCompatible.integral_eq_integral_smul_comp (hH : IsClosed (H : Set G))
    (hν : IsCompatible H μG μH ν) {ρ : G → ℝ≥0∞} (hρ : IsNormalizingFunction H μH ρ)
    {φ : LeftQuotient H → E} (hφ : AEStronglyMeasurable φ ν) :
    ∫ q, φ q ∂ν = ∫ g, (ρ g).toReal • φ (leftQuotientMap H g) ∂μG := by
  have hπ : Measurable (leftQuotientMap H) := continuous_quotient_mk'.measurable
  have hfin := hρ.ae_lt_top hH hν
  rw [hν.eq_map_withDensity hH hρ] at hφ ⊢
  rw [integral_map hπ.aemeasurable hφ,
    integral_withDensity_eq_integral_toReal_smul hρ.measurable hfin]

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [MeasurableSpace H] [BorelSpace H] in
/-- The function descended from a measurable left `H`-invariant function is measurable. -/
theorem measurable_descend (hH : IsClosed (H : Set G)) {Y : Type*} [MeasurableSpace Y]
    (F : G → Y) (hFm : Measurable F) (hF : ∀ h : H, ∀ g, F (h.val * g) = F g) :
    Measurable (descend H F hF) :=
  (measurable_quotient_iff H hH _).2 hFm

/-- **The rule for integrability of an invariant function**: for a normalizing `ρ` and a
measurable left `H`-invariant `F`, the descended function is `ν`-integrable exactly when
`g ↦ ρ g • F g` is `μG`-integrable. -/
theorem IsCompatible.integrable_descend_iff (hH : IsClosed (H : Set G))
    (hν : IsCompatible H μG μH ν) {ρ : G → ℝ≥0∞} (hρ : IsNormalizingFunction H μH ρ)
    (F : G → E) (hFm : Measurable F) (hF : ∀ h : H, ∀ g, F (h.val * g) = F g) :
    Integrable (descend H F hF) ν ↔ Integrable (fun g => (ρ g).toReal • F g) μG :=
  hν.integrable_iff_integrable_smul_comp hH hρ
    (measurable_descend hH F hFm hF).aestronglyMeasurable

/-- **The rule for the integral of an invariant function**: for a normalizing `ρ` and a
measurable left `H`-invariant `F`, `∫ q, (descend F) q ∂ν = ∫ g, ρ g • F g ∂μG`. -/
theorem IsCompatible.integral_descend_eq (hH : IsClosed (H : Set G))
    (hν : IsCompatible H μG μH ν) {ρ : G → ℝ≥0∞} (hρ : IsNormalizingFunction H μH ρ)
    (F : G → E) (hFm : Measurable F) (hF : ∀ h : H, ∀ g, F (h.val * g) = F g) :
    ∫ q, descend H F hF q ∂ν = ∫ g, (ρ g).toReal • F g ∂μG :=
  hν.integral_eq_integral_smul_comp hH hρ
    (measurable_descend hH F hFm hF).aestronglyMeasurable

/-- The right-hand side of the rule does not depend on the normalizing function. -/
theorem IsCompatible.lintegral_mul_eq_of_isNormalizingFunction (hH : IsClosed (H : Set G))
    (hν : IsCompatible H μG μH ν) {ρ₁ ρ₂ : G → ℝ≥0∞} (hρ₁ : IsNormalizingFunction H μH ρ₁)
    (hρ₂ : IsNormalizingFunction H μH ρ₂) (F : G → ℝ≥0∞) (hFm : Measurable F)
    (hF : ∀ h : H, ∀ g, F (h.val * g) = F g) :
    ∫⁻ g, F g * ρ₁ g ∂μG = ∫⁻ g, F g * ρ₂ g ∂μG := by
  rw [← hν.lintegral_descend_eq hH hρ₁ F hFm hF, hν.lintegral_descend_eq hH hρ₂ F hFm hF]

/-- The right-hand side of the integral rule does not depend on the normalizing function. -/
theorem IsCompatible.integral_smul_eq_of_isNormalizingFunction (hH : IsClosed (H : Set G))
    (hν : IsCompatible H μG μH ν) {ρ₁ ρ₂ : G → ℝ≥0∞} (hρ₁ : IsNormalizingFunction H μH ρ₁)
    (hρ₂ : IsNormalizingFunction H μH ρ₂) (F : G → E) (hFm : Measurable F)
    (hF : ∀ h : H, ∀ g, F (h.val * g) = F g) :
    ∫ g, (ρ₁ g).toReal • F g ∂μG = ∫ g, (ρ₂ g).toReal • F g ∂μG := by
  rw [← hν.integral_descend_eq hH hρ₁ F hFm hF, hν.integral_descend_eq hH hρ₂ F hFm hF]

end Weil

section Existence

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [SigmaCompactSpace G]

/-- A continuous `β ≥ 0` that does not vanish identically on any coset `H x`, and whose
nonvanishing points in `H · C` lie in a compact set for each compact `C`. It is the locally finite
sum of Urysohn functions equal to `1` on `K (m + 2) \ H · interior (K (m + 1))` and to `0` on
`H · K m`, for a compact exhaustion `K` with `K 0 = K 1 = ∅`. -/
private theorem exists_bump (H : Subgroup G) (hH : IsClosed (H : Set G)) :
    ∃ β : G → ℝ, Continuous β ∧ (∀ x, 0 ≤ β x) ∧ (∀ x, ∃ h ∈ H, β (h * x) ≠ 0) ∧
      ∀ C : Set G, IsCompact C → ∃ C' : Set G, IsCompact C' ∧
        ∀ h ∈ H, ∀ x ∈ C, β (h * x) ≠ 0 → h * x ∈ C' := by
  classical
  let K : CompactExhaustion G := (CompactExhaustion.choice G).shiftr.shiftr
  have hK0 : K 0 = ∅ := rfl
  have hK1 : K 1 = ∅ := rfl
  let S : ℕ → Set G := fun m => (H : Set G) * K m
  let O : ℕ → Set G := fun m => (H : Set G) * interior (K m)
  have hSc : ∀ m, IsClosed (S m) := fun m => hH.mul_right_of_isCompact (K.isCompact m)
  have hOo : ∀ m, IsOpen (O m) := fun m => isOpen_interior.mul_left
  have hQ : ∀ m, IsCompact (K (m + 2) \ O (m + 1)) := fun m => (K.isCompact _).diff (hOo _)
  have hSO : ∀ m, S m ⊆ O (m + 1) := fun m => Set.mul_subset_mul_left (K.subset_interior_succ m)
  have hd : ∀ m, Disjoint (K (m + 2) \ O (m + 1)) (S m) := fun m =>
    Set.disjoint_left.2 fun x hx hxS => hx.2 (hSO m hxS)
  choose f hf1 hf0 hfc hfI using fun m =>
    exists_continuous_one_zero_of_isCompact (hQ m) (hSc m) (hd m)
  have hself : ∀ m, K m ⊆ S m := fun m x hx => ⟨1, H.one_mem, x, hx, one_mul x⟩
  have hSmono : ∀ {a b : ℕ}, a ≤ b → S a ⊆ S b := fun hab =>
    Set.mul_subset_mul_left (K.subset hab)
  have hvan : ∀ {N m : ℕ}, N ≤ m → ∀ x ∈ S N, f m x = 0 := fun hNm x hx =>
    hf0 _ (hSmono hNm hx)
  have hnn : ∀ m x, 0 ≤ f m x := fun m x => (hfI m x).1
  have hlf : LocallyFinite fun m => Function.support (f m) := by
    intro x
    obtain ⟨n, hn⟩ := K.exists_mem x
    refine ⟨interior (K (n + 1)), isOpen_interior.mem_nhds (K.subset_interior_succ n hn),
      (Set.finite_lt_nat (n + 1)).subset ?_⟩
    rintro m ⟨y, hy, hyU⟩
    by_contra hm
    exact hy (hvan (not_lt.1 hm) y (hself _ (interior_subset hyU)))
  have hfin : ∀ x, (Function.support fun m => f m x).Finite := by
    intro x
    obtain ⟨n, hn⟩ := K.exists_mem x
    refine (Set.finite_lt_nat n).subset ?_
    intro m hm
    by_contra hmn
    exact hm (hvan (not_lt.1 hmn) x (hself _ hn))
  refine ⟨fun x => ∑ᶠ m, f m x, continuous_finsum (fun m => (f m).continuous) hlf,
    fun x => finsum_nonneg fun m => hnn m x, ?_, ?_⟩
  · intro x
    have hex : ∃ n, x ∈ O n := by
      obtain ⟨n, hn⟩ := K.exists_mem x
      exact ⟨n + 1, 1, H.one_mem, x, K.subset_interior_succ n hn, one_mul x⟩
    have hspec := Nat.find_spec hex
    have hmin : ∀ n, n < Nat.find hex → x ∉ O n := fun n hn => Nat.find_min hex hn
    obtain ⟨m, hm⟩ : ∃ m, Nat.find hex = m + 2 := by
      rcases hN : Nat.find hex with _ | _ | m
      · rw [hN] at hspec
        obtain ⟨h, -, y, hy, -⟩ := hspec
        simp [hK0] at hy
      · rw [hN] at hspec
        obtain ⟨h, -, y, hy, -⟩ := hspec
        simp [hK1] at hy
      · exact ⟨m, rfl⟩
    rw [hm] at hspec
    obtain ⟨h, hh, y, hy, rfl⟩ := hspec
    have hyQ : y ∈ K (m + 2) \ O (m + 1) := by
      refine ⟨interior_subset hy, ?_⟩
      rintro ⟨h', hh', z, hz, rfl⟩
      exact hmin (m + 1) (by omega) ⟨h * h', H.mul_mem hh hh', z, hz, mul_assoc _ _ _⟩
    refine ⟨h⁻¹, H.inv_mem hh, ?_⟩
    rw [inv_mul_cancel_left]
    have h1 : f m y ≤ ∑ᶠ m, f m y := single_le_finsum m (hfin y) (fun j => hnn j y)
    have h2 : f m y = 1 := hf1 m hyQ
    intro h0
    simp only [h0, h2] at h1
    linarith
  · intro C hC
    obtain ⟨N, hN⟩ := K.exists_superset_of_isCompact hC
    refine ⟨⋃ m ∈ Finset.range N, tsupport (f m),
      (Finset.range N).isCompact_biUnion fun m _ => hfc m, ?_⟩
    intro h hh x hx hne
    obtain ⟨m, hm⟩ : ∃ m, f m (h * x) ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hne (finsum_eq_zero_of_forall_eq_zero hall)
    have hmN : m < N := by
      by_contra hmN
      exact hm (hvan (not_lt.1 hmN) _ ⟨h, hh, x, hN hx, rfl⟩)
    exact Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_range.2 hmN)) (subset_tsupport _ hm)

variable [MeasurableSpace G] [BorelSpace G]

/-- **Existence of a normalizing function** for a closed subgroup `H` of a σ-compact locally
compact group, with a right-invariant measure `μH` finite on compacts and positive on open sets:
there is a continuous `ρ : G → ℝ≥0` with `∫⁻ h, ρ (h g) ∂μH = 1` for every `g`, such that for every
compact `C` the points `h x` (`h ∈ H`, `x ∈ C`) where `ρ` does not vanish lie in a compact set. -/
theorem exists_continuous_isNormalizingFunction (H : Subgroup G) (hH : IsClosed (H : Set G))
    [MeasurableSpace H] [BorelSpace H] (μH : Measure H) [μH.IsMulRightInvariant]
    [IsFiniteMeasureOnCompacts μH] [μH.IsOpenPosMeasure] :
    ∃ ρ : G → ℝ≥0, Continuous ρ ∧ IsNormalizingFunction H μH (fun g => (ρ g : ℝ≥0∞)) ∧
      ∀ C : Set G, IsCompact C → ∃ C' : Set G, IsCompact C' ∧
        ∀ h : H, ∀ x ∈ C, ρ (h.val * x) ≠ 0 → h.val * x ∈ C' := by
  obtain ⟨β, hβ, hβ0, hcov, hsupp⟩ := exists_bump H hH
  have hB : ∀ C : Set G, IsCompact C → ∃ B : Set H, IsCompact B ∧
      ∀ t : H, ∀ x ∈ C, β (t.val * x) ≠ 0 → t ∈ B := by
    intro C hC
    obtain ⟨C', hC', h⟩ := hsupp C hC
    refine ⟨Subtype.val ⁻¹' (C' * C⁻¹),
      hH.isClosedEmbedding_subtypeVal.isCompact_preimage (hC'.mul hC.inv), fun t x hx hne => ?_⟩
    exact ⟨t.val * x, h _ t.2 x hx hne, x⁻¹, Set.inv_mem_inv.2 hx, by simp⟩
  have hcx : ∀ x, Continuous fun t : H => β (t.val * x) := fun x =>
    hβ.comp (continuous_subtype_val.mul continuous_const)
  have hcs : ∀ x, HasCompactSupport fun t : H => β (t.val * x) := by
    intro x
    obtain ⟨B, hBc, hB'⟩ := hB {x} isCompact_singleton
    refine HasCompactSupport.intro hBc fun t ht => ?_
    by_contra hne
    exact ht (hB' t x rfl hne)
  let D : G → ℝ := fun x => ∫ t : H, β (t.val * x) ∂μH
  have hDc : Continuous D := by
    rw [continuous_iff_continuousAt]
    intro x₀
    obtain ⟨N, hNc, hN⟩ := exists_compact_mem_nhds x₀
    obtain ⟨B, hBc, hB'⟩ := hB N hNc
    have hc : ContinuousOn (Function.uncurry fun (x : G) (t : H) => β (t.val * x)) (N ×ˢ univ) :=
      (hβ.comp ((continuous_subtype_val.comp continuous_snd).mul continuous_fst)).continuousOn
    have hz : ∀ x, ∀ t : H, x ∈ N → t ∉ B → β (t.val * x) = 0 := by
      intro x t hx ht
      by_contra hne
      exact ht (hB' t x hx hne)
    exact (continuousOn_integral_of_compact_support (μ := μH) hBc hc hz).continuousAt hN
  have hDpos : ∀ x, 0 < D x := by
    intro x
    obtain ⟨h, hh, hne⟩ := hcov x
    exact (hcx x).integral_pos_of_hasCompactSupport_nonneg_nonzero (hcs x)
      (fun t => hβ0 _) (x := ⟨h, hh⟩) hne
  have hDinv : ∀ (s : H) (x : G), D (s.val * x) = D x := by
    intro s x
    simpa only [D, Subgroup.coe_mul, mul_assoc] using
      integral_mul_right_eq_self (μ := μH) (fun t : H => β (t.val * x)) s
  have hρc : Continuous fun x => Real.toNNReal (β x / D x) :=
    continuous_real_toNNReal.comp (hβ.div hDc fun x => (hDpos x).ne')
  refine ⟨fun x => Real.toNNReal (β x / D x), hρc, ⟨?_, ?_⟩, ?_⟩
  · exact (ENNReal.continuous_coe.comp hρc).measurable
  · intro x
    have hint : Integrable (fun t : H => β (t.val * x) / D x) μH :=
      ((hcx x).integrable_of_hasCompactSupport (hcs x)).div_const _
    have h1 : ∫⁻ t : H, ((Real.toNNReal (β (t.val * x) / D (t.val * x)) : ℝ≥0) : ℝ≥0∞) ∂μH =
        ∫⁻ t : H, ENNReal.ofReal (β (t.val * x) / D x) ∂μH := by
      refine lintegral_congr fun t => ?_
      rw [hDinv]
      rfl
    rw [h1, ← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun t => div_nonneg (hβ0 _) (hDpos x).le), integral_div]
    change ENNReal.ofReal (D x / D x) = 1
    rw [div_self (hDpos x).ne', ENNReal.ofReal_one]
  · intro C hC
    obtain ⟨C', hC', h⟩ := hsupp C hC
    refine ⟨C', hC', fun t x hx hne => h _ t.2 x hx fun h0 => hne ?_⟩
    simp [h0]

end Existence

end Langlands.QuotientIntegration

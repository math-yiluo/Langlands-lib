import Langlands.HarmonicAnalysis.Distribution.RenardCenterStatements
import Langlands.HarmonicAnalysis.Distribution.RenardConvolutionProof
import Langlands.Representation.Hecke.CommonInvarianceProof
import Langlands.Representation.Hecke.FiniteSampling
import Langlands.Representation.Hecke.NormalizedIndicator

/-! # Renard II.3.13: translation, trace and sandwich criteria for conjugation invariance -/

noncomputable section

open MeasureTheory

namespace Langlands.HarmonicAnalysis.Distribution.RenardCenter

universe uG

section Subgroups

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Conjugates of a small open subgroup by a compact set stay in a given open subgroup. -/
theorem exists_openSubgroup_conj_mem (C : Set G) (hC : IsCompact C) (K : OpenSubgroup G) :
    ∃ U : OpenSubgroup G, ∀ y ∈ C, ∀ k ∈ U, y * k * y⁻¹ ∈ K := by
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover
    (fun y : G => (fun z => z * y⁻¹) ⁻¹' (K : Set G))
    (fun y => K.isOpen.preimage (continuous_id.mul continuous_const))
    (fun z _ => Set.mem_iUnion.2 ⟨z, by simp⟩)
  let conj (y : G) : OpenSubgroup G :=
    K.comap (MulAut.conj y).toMonoidHom
      (by
        change Continuous (fun x => y * x * y⁻¹)
        exact (continuous_const.mul continuous_id).mul continuous_const)
  refine ⟨t.inf conj, ?_⟩
  intro z hz k hk
  obtain ⟨y, hy, hzy⟩ := Set.mem_iUnion₂.1 (ht hz)
  have hyk : y * k * y⁻¹ ∈ K := by
    have h1 : k ∈ conj y := Finset.inf_le (f := conj) hy hk
    exact OpenSubgroup.mem_comap.1 h1
  have hzy' : z * y⁻¹ ∈ K := hzy
  have : z * k * z⁻¹ = (z * y⁻¹) * (y * k * y⁻¹) * (z * y⁻¹)⁻¹ := by group
  rw [this]
  exact K.mul_mem (K.mul_mem hzy' hyk) (K.inv_mem hzy')

/-- The open subgroup of elements conjugated by `g` into a given open subgroup. -/
def conjPreimage (g : G) (K : OpenSubgroup G) : OpenSubgroup G :=
  K.comap (MulAut.conj g).toMonoidHom
    (by
      change Continuous (fun x => g * x * g⁻¹)
      exact (continuous_const.mul continuous_id).mul continuous_const)

theorem mem_conjPreimage {g : G} {K : OpenSubgroup G} {k : G} :
    k ∈ conjPreimage g K ↔ g * k * g⁻¹ ∈ K :=
  OpenSubgroup.mem_comap

end Subgroups

section Translation

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Conjugating a left translate by the same element gives the right translate. -/
theorem pullback_conj_leftTranslate (g : G) (f : SchwartzBruhat G) :
    Hecke.TestFunction.pullback (conjugationHomeomorph g)
        (Hecke.TestFunction.leftTranslate g f) =
      Hecke.TestFunction.rightTranslate g⁻¹ f := by
  ext x
  simp [mul_assoc]

/-- Conjugation invariance is the Dirac translation identity. -/
theorem isConjugationInvariant_iff_translation (T : Distribution G) :
    IsConjugationInvariant T ↔ TranslationCondition T := by
  rw [isConjugationInvariant_iff]
  constructor
  · intro hT g f
    rw [← pullback_conj_leftTranslate, hT]
  · intro hT a F
    have hF : Hecke.TestFunction.leftTranslate a (Hecke.TestFunction.leftTranslate a⁻¹ F) = F := by
      rw [← Hecke.TestFunction.leftTranslate_mul, mul_inv_cancel,
        Hecke.TestFunction.leftTranslate_one]
    calc T (Hecke.TestFunction.pullback (conjugationHomeomorph a) F)
        = T (Hecke.TestFunction.rightTranslate a⁻¹ (Hecke.TestFunction.leftTranslate a⁻¹ F)) := by
          rw [← pullback_conj_leftTranslate, hF]
      _ = T (Hecke.TestFunction.leftTranslate a (Hecke.TestFunction.leftTranslate a⁻¹ F)) :=
          (hT a _).symm
      _ = T F := by rw [hF]

end Translation

section Sampling

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [MeasurableSpace G] [OpensMeasurableSpace G]

/-- The finite sampling weights, cut off outside the support of the test. -/
def sampleWeight (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    (K : OpenSubgroup G) (h : SchwartzBruhat G) (hh : ∀ (k : K) g, h (g * (k : G)) = h g)
    (i : Fin (Hecke.fixedLevelActionSamples μ K h hh).size) : ℂ :=
  (Hecke.fixedLevelActionSamples μ K h hh).coefficients i *
    (if h ((Hecke.fixedLevelActionSamples μ K h hh).points i) = 0 then 0 else 1)

/-- Finite sampling of `∫ h φ`, where `φ` need only be right invariant at
points of the support of `h`. -/
theorem integral_eq_sampleWeight (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    (K : OpenSubgroup G) (h : SchwartzBruhat G) (hh : ∀ (k : K) g, h (g * (k : G)) = h g)
    (φ : G → ℂ) (hφ : ∀ y, h y ≠ 0 → ∀ k : K, φ (y * (k : G)) = φ y) :
    (∫ y, h y * φ y ∂μ) =
      ∑ i, sampleWeight μ K h hh i * φ ((Hecke.fixedLevelActionSamples μ K h hh).points i) := by
  classical
  let a : G → ℂ := fun y => if h y = 0 then 0 else φ y
  have ha : ∀ (k : K) g, a (g * (k : G)) = a g := by
    intro k g
    simp only [a, hh k g]
    split_ifs with hg
    · rfl
    · exact hφ g hg k
  have hint : (fun y => h y * φ y) = fun y => h y * a y := by
    funext y
    simp only [a]
    split_ifs with hy <;> simp [hy]
  rw [hint, Hecke.fixedLevelActionSamples_integral μ K h hh a ha]
  apply Finset.sum_congr rfl
  intro i _
  simp only [a, sampleWeight]
  split_ifs <;> ring

end Sampling

section Level

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]

/-- A common sampling level for a test `f` and a weight `h`: `h` is right
invariant, `f` is left invariant, and `f` is right invariant under the
conjugates of the level by points of the support of `h`. -/
theorem exists_sampling_level (f h : SchwartzBruhat G) :
    ∃ K : OpenSubgroup G,
      (∀ (k : K) g, h (g * (k : G)) = h g) ∧
      (∀ (k : K) x, f ((k : G) * x) = f x) ∧
      (∀ y, h y ≠ 0 → ∀ (k : K) x, f (x * (y * (k : G) * y⁻¹)) = f x) := by
  classical
  obtain ⟨K₀, -, -, hK₀⟩ := Hecke.TestFunction.commonCompactOpenBiInvariance G {f, h} ⊤
  have hf0 := hK₀ f (by simp)
  have hh0 := hK₀ h (by simp)
  obtain ⟨U, hU⟩ := exists_openSubgroup_conj_mem (Function.support (h : G → ℂ))
    (Hecke.TestFunction.isCompact_support h) K₀
  refine ⟨K₀ ⊓ U, ?_, ?_, ?_⟩
  · intro k g
    exact hh0.2 ⟨k, (OpenSubgroup.mem_inf.1 k.2).1⟩ g
  · intro k x
    exact hf0.1 ⟨k, (OpenSubgroup.mem_inf.1 k.2).1⟩ x
  · intro y hy k x
    exact hf0.2 ⟨y * k * y⁻¹, hU y hy k (OpenSubgroup.mem_inf.1 k.2).2⟩ x

end Level

section CompactAverage

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]

omit [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] in
/-- The normalized compact-subgroup integral of a test constant on the subgroup. -/
theorem compactSubgroupDistribution_eq_of_const (K : Subgroup G) (hK : IsCompact (K : Set G))
    (F : SchwartzBruhat G) (c : ℂ) (hF : ∀ k ∈ K, F k = c) :
    compactSubgroupDistribution K hK F = c := by
  let _ : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let _ : MeasurableSpace K := borel K
  let _ : BorelSpace K := ⟨rfl⟩
  change (∫ k : K, F k.val ∂(Measure.haarMeasure ⊤)) = c
  have hc : (fun k : K => F k.val) = fun _ => c := funext fun k => hF k.val k.property
  have h1 : (Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts K)) Set.univ = 1 := by
    simpa using Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts K))
  rw [hc, integral_const]
  simp [Measure.real, h1]

/-- `e_K * f = f` for left `K`-invariant tests. -/
theorem leftConvolveTest_compactSubgroupHaar (K : Subgroup G) (hK : IsCompact (K : Set G))
    (f : SchwartzBruhat G) (hf : ∀ k ∈ K, ∀ x, f (k * x) = f x) :
    leftConvolveTest (compactSubgroupHaar K hK : Distribution G) f = f := by
  funext x
  change compactSubgroupDistribution K hK
    (Hecke.TestFunction.leftTranslate x (Hecke.TestFunction.inversion f)) = f x
  refine compactSubgroupDistribution_eq_of_const K hK _ _ fun k hk => ?_
  simpa [mul_inv_rev] using hf k⁻¹ (K.inv_mem hk) x

/-- `f * e_K = f` for right `K`-invariant tests. -/
theorem rightConvolveTest_compactSubgroupHaar (K : Subgroup G) (hK : IsCompact (K : Set G))
    (f : SchwartzBruhat G) (hf : ∀ k ∈ K, ∀ x, f (x * k) = f x) :
    rightConvolveTest f (compactSubgroupHaar K hK : Distribution G) = f := by
  funext x
  change compactSubgroupDistribution K hK
    (Hecke.TestFunction.rightTranslate x⁻¹ (Hecke.TestFunction.inversion f)) = f x
  refine compactSubgroupDistribution_eq_of_const K hK _ _ fun k hk => ?_
  simpa [mul_inv_rev] using hf k⁻¹ (K.inv_mem hk) x

end CompactAverage

section Indicator

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]

/-- Integrating against the normalized indicator of `gK` evaluates at `g`
any function that is constant on `gK`. -/
theorem integral_leftTranslate_indicator (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (g : G) (a : G → ℂ) (ha : ∀ k ∈ K, a (g * k) = a g) :
    (∫ y, ((μ.real (K : Set G) : ℂ)⁻¹ *
        (K : Set G).indicator (fun _ => (1 : ℂ)) (g⁻¹ * y)) * a y ∂μ) = a g := by
  rw [← integral_mul_left_eq_self _ g]
  simp only [inv_mul_cancel_left]
  have hfun : (fun y => ((μ.real (K : Set G) : ℂ)⁻¹ *
        (K : Set G).indicator (fun _ => (1 : ℂ)) y) * a (g * y)) =
      (K : Set G).indicator (fun _ => (μ.real (K : Set G) : ℂ)⁻¹ * a g) := by
    funext y
    by_cases hy : y ∈ (K : Set G)
    · simp [hy, ha y hy]
    · simp [hy]
  rw [hfun, integral_indicator K.isOpen.measurableSet, setIntegral_const, Complex.real_smul]
  have hne := Hecke.HeckeAlgebra.compactOpen_complex_mass_ne_zero μ K hK
  field_simp

end Indicator

section Trace

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
variable [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]

omit [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] in
theorem rightConvolveTest_heckeDistribution (h : Hecke.HeckeAlgebra μ) (f : SchwartzBruhat G)
    (x : G) : rightConvolveTest f (heckeDistribution μ h) x = ∫ y, h y * f (x * y⁻¹) ∂μ := by
  simp [rightConvolveTest]

omit [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] in
theorem leftConvolveTest_heckeDistribution (h : Hecke.HeckeAlgebra μ) (f : SchwartzBruhat G)
    (x : G) : leftConvolveTest (heckeDistribution μ h) f x = ∫ y, h y * f (y⁻¹ * x) ∂μ := by
  simp [leftConvolveTest]

/-- Translation invariance gives the trace identity: both scalar convolutions
are the same finite combination of left, respectively right, translates. -/
theorem trace_of_translation (T : Distribution G) (hT : TranslationCondition T) :
    TraceCondition μ T := by
  classical
  intro f h
  let h' : SchwartzBruhat G := Hecke.HeckeAlgebra.toTestFunction μ h
  obtain ⟨K, hh, hfl, hfr⟩ := exists_sampling_level f h'
  let S := Hecke.fixedLevelActionSamples μ K h' hh
  refine ⟨∑ i, sampleWeight μ K h' hh i • Hecke.TestFunction.rightTranslate (S.points i)⁻¹ f,
    ∑ i, sampleWeight μ K h' hh i • Hecke.TestFunction.leftTranslate (S.points i) f,
    ?_, ?_, ?_⟩
  · funext x
    rw [rightConvolveTest_heckeDistribution]
    change _ = ∫ y, h' y * f (x * y⁻¹) ∂μ
    rw [integral_eq_sampleWeight μ K h' hh (fun y => f (x * y⁻¹))]
    · simp [S, Finset.sum_apply]
    · intro y hy k
      have := hfr y hy k⁻¹ (x * y⁻¹)
      simpa [mul_assoc, mul_inv_rev] using this
  · funext x
    rw [leftConvolveTest_heckeDistribution]
    change _ = ∫ y, h' y * f (y⁻¹ * x) ∂μ
    rw [integral_eq_sampleWeight μ K h' hh (fun y => f (y⁻¹ * x))]
    · simp [S, Finset.sum_apply]
    · intro y _ k
      have := hfl k⁻¹ (y⁻¹ * x)
      simpa [mul_assoc, mul_inv_rev] using this
  · rw [map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, map_smul, hT]

/-- The trace identity for the normalized indicator of `gK`, with `K` small,
is the Dirac translation identity. -/
theorem translation_of_trace (T : Distribution G) (hT : TraceCondition μ T) :
    TranslationCondition T := by
  classical
  intro g f
  obtain ⟨K₀, -, -, hK₀⟩ := Hecke.TestFunction.commonCompactOpenBiInvariance G {f} ⊤
  have hf0 := hK₀ f (by simp)
  obtain ⟨K, hKle, hKc, -⟩ :=
    Hecke.TestFunction.commonCompactOpenBiInvariance G ∅ (K₀ ⊓ conjPreimage g K₀)
  let h : Hecke.HeckeAlgebra μ := ((μ.real (K : Set G) : ℂ)⁻¹) •
    Hecke.TestFunction.leftTranslate g (Hecke.TestFunction.subgroupIndicator K hKc)
  have hval : ∀ y, h y = (μ.real (K : Set G) : ℂ)⁻¹ *
      (K : Set G).indicator (fun _ => (1 : ℂ)) (g⁻¹ * y) := fun y => rfl
  obtain ⟨fh, hf, hfh, hhf, hTe⟩ := hT f h
  have e1 : fh = Hecke.TestFunction.rightTranslate g⁻¹ f := by
    ext x
    rw [hfh, rightConvolveTest_heckeDistribution]
    simp only [hval]
    refine (integral_leftTranslate_indicator μ K hKc g (fun y => f (x * y⁻¹)) ?_).trans ?_
    · intro k hk
      have hk' := OpenSubgroup.mem_inf.1 (hKle hk)
      have := hf0.2 ⟨g * k⁻¹ * g⁻¹, mem_conjPreimage.1 ((conjPreimage g K₀).inv_mem hk'.2)⟩
        (x * g⁻¹)
      simpa [mul_assoc, mul_inv_rev] using this
    · simp
  have e2 : hf = Hecke.TestFunction.leftTranslate g f := by
    ext x
    rw [hhf, leftConvolveTest_heckeDistribution]
    simp only [hval]
    refine (integral_leftTranslate_indicator μ K hKc g (fun y => f (y⁻¹ * x)) ?_).trans ?_
    · intro k hk
      have hk' := OpenSubgroup.mem_inf.1 (hKle hk)
      have := hf0.1 ⟨k⁻¹, K₀.inv_mem hk'.1⟩ (g⁻¹ * x)
      simpa [mul_assoc, mul_inv_rev] using this
    · simp
  rw [← e1, ← e2]
  exact hTe.symm

end Trace

section Sandwich

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]

omit [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] in
theorem leftConvolveTest_dirac (g : G) (f : SchwartzBruhat G) :
    leftConvolveTest (dirac g) f = Hecke.TestFunction.leftTranslate g f := by
  funext x
  simp [leftConvolveTest]

omit [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] in
theorem rightConvolveTest_dirac (g : G) (f : SchwartzBruhat G) :
    rightConvolveTest f (dirac g) = Hecke.TestFunction.rightTranslate g⁻¹ f := by
  funext x
  simp [rightConvolveTest]

/-- With the local-unit hypotheses, `(e * δ_g * e) * f = L_g f`. -/
theorem leftConvolveTest_sandwich (e : compactlySupported (X := G)) (g : G)
    (f : SchwartzBruhat G)
    (h1 : leftConvolveTest (e : Distribution G) f = f)
    (h2 : leftConvolveTest (e : Distribution G) (Hecke.TestFunction.leftTranslate g f) =
      Hecke.TestFunction.leftTranslate g f) :
    leftConvolveTest (convolution (convolution e (compactDirac g)) e : Distribution G) f =
      Hecke.TestFunction.leftTranslate g f := by
  have hA : leftSmoothFunction e ⟨(f : G → ℂ), f.locallyConstant⟩ =
      ⟨(f : G → ℂ), f.locallyConstant⟩ := by
    ext x
    change leftConvolveSmooth e _ x = f x
    rw [leftConvolveSmooth_eq_test, h1]
  have hB : leftSmoothFunction (compactDirac g) ⟨(f : G → ℂ), f.locallyConstant⟩ =
      ⟨(Hecke.TestFunction.leftTranslate g f : G → ℂ),
        (Hecke.TestFunction.leftTranslate g f).locallyConstant⟩ := by
    ext x
    change leftConvolveSmooth (compactDirac g) _ x = _
    rw [leftConvolveSmooth_eq_test, coe_compactDirac, leftConvolveTest_dirac]
    rfl
  rw [← leftConvolveSmooth_eq_test, leftConvolveSmooth_associative,
    leftConvolveSmooth_associative, hA, hB, leftConvolveSmooth_eq_test, h2]

/-- With the local-unit hypotheses, `f * (e * δ_g * e) = R_{g⁻¹} f`. -/
theorem rightConvolveTest_sandwich (e : compactlySupported (X := G)) (g : G)
    (f : SchwartzBruhat G)
    (h1 : rightConvolveTest f (e : Distribution G) = f)
    (h2 : rightConvolveTest (Hecke.TestFunction.rightTranslate g⁻¹ f) (e : Distribution G) =
      Hecke.TestFunction.rightTranslate g⁻¹ f) :
    rightConvolveTest f (convolution (convolution e (compactDirac g)) e : Distribution G) =
      Hecke.TestFunction.rightTranslate g⁻¹ f := by
  have hA : rightSmoothFunction ⟨(f : G → ℂ), f.locallyConstant⟩ e =
      ⟨(f : G → ℂ), f.locallyConstant⟩ := by
    ext x
    change rightConvolveSmooth _ e x = f x
    rw [rightConvolveSmooth_eq_test, h1]
  have hB : rightSmoothFunction ⟨(f : G → ℂ), f.locallyConstant⟩
        (convolution e (compactDirac g)) =
      ⟨(Hecke.TestFunction.rightTranslate g⁻¹ f : G → ℂ),
        (Hecke.TestFunction.rightTranslate g⁻¹ f).locallyConstant⟩ := by
    ext x
    change rightConvolveSmooth _ (convolution e (compactDirac g)) x = _
    rw [← rightConvolveSmooth_associative, hA, rightConvolveSmooth_eq_test, coe_compactDirac,
      rightConvolveTest_dirac]
    rfl
  rw [← rightConvolveSmooth_eq_test, ← rightConvolveSmooth_associative, hB,
    rightConvolveSmooth_eq_test, h2]

/-- Translation invariance gives the compact-open sandwich identity. -/
theorem sandwich_of_translation (T : Distribution G) (hT : TranslationCondition T) :
    SandwichTraceCondition T := by
  intro f g K hK e h1 h2 h3 h4
  exact ⟨_, _, (leftConvolveTest_sandwich _ g f h1 h3).symm,
    (rightConvolveTest_sandwich _ g f h2 h4).symm, hT g f⟩

/-- The sandwich identity, at a level fixing `f` and both of its translates,
gives the translation identity. -/
theorem translation_of_sandwich (T : Distribution G) (hT : SandwichTraceCondition T) :
    TranslationCondition T := by
  classical
  intro g f
  obtain ⟨K, -, hKc, hK⟩ := Hecke.TestFunction.commonCompactOpenBiInvariance G
    {f, Hecke.TestFunction.leftTranslate g f, Hecke.TestFunction.rightTranslate g⁻¹ f} ⊤
  have hf := hK f (by simp)
  have hl := hK (Hecke.TestFunction.leftTranslate g f) (by simp)
  have hr := hK (Hecke.TestFunction.rightTranslate g⁻¹ f) (by simp)
  have e1 := leftConvolveTest_compactSubgroupHaar K.toSubgroup hKc f
    (fun k hk x => hf.1 ⟨k, hk⟩ x)
  have e2 := rightConvolveTest_compactSubgroupHaar K.toSubgroup hKc f
    (fun k hk x => hf.2 ⟨k, hk⟩ x)
  have e3 := leftConvolveTest_compactSubgroupHaar K.toSubgroup hKc
    (Hecke.TestFunction.leftTranslate g f) (fun k hk x => hl.1 ⟨k, hk⟩ x)
  have e4 := rightConvolveTest_compactSubgroupHaar K.toSubgroup hKc
    (Hecke.TestFunction.rightTranslate g⁻¹ f) (fun k hk x => hr.2 ⟨k, hk⟩ x)
  obtain ⟨l, r, hl', hr', hTe⟩ := hT f g K hKc e1 e2 e3 e4
  have el : l = Hecke.TestFunction.leftTranslate g f := by
    ext x
    rw [hl', leftConvolveTest_sandwich _ g f e1 e3]
  have er : r = Hecke.TestFunction.rightTranslate g⁻¹ f := by
    ext x
    rw [hr', rightConvolveTest_sandwich _ g f e2 e4]
  rw [← el, ← er]
  exact hTe

end Sandwich

/-- The first conjunct of II.3.13: the translation, trace and sandwich
criteria for conjugation invariance of an arbitrary algebraic distribution. -/
theorem criteria : CriteriaStatement.{uG} := by
  intro G _ _ _ _ _ _ _ _ μ _ T
  have h1 := isConjugationInvariant_iff_translation T
  exact ⟨h1, h1.trans ⟨trace_of_translation μ T, translation_of_trace μ T⟩,
    h1.trans ⟨sandwich_of_translation T, translation_of_sandwich T⟩⟩

end Langlands.HarmonicAnalysis.Distribution.RenardCenter

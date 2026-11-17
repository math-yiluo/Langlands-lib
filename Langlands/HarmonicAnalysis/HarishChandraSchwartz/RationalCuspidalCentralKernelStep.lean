import Langlands.HarmonicAnalysis.HarishChandraSchwartz.SchwartzCompactLifting
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.KernelQuotient
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCuspidalCentralImage
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.Translations
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSquareIntegrableDecay
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalDiscreteSeriesOrbitFiniteness
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.CentralProjectionSquareIntegrable
import Langlands.Analysis.Local.QuotientMeasureExistence
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalXiSquareIntegrable

/-! # The local kernel step of Waldspurger VIII.4.1

Waldspurger proves VIII.4.1 (printed pp. 327–330) with the cuspidal projection `°e` of the
characteristic function `e` of `H`. This module isolates that step. The structure
`IsRationalCuspidalLevelKernel` lists the properties of `°e` that the proof uses. The theorem
`IsRationalCuspidalLevelKernel.finiteDimensional_levelSpan` proves that the actual central level
span is finite dimensional from them. It feeds the Library's abstract kernel theorem
`finiteDimensional_of_kernelAlphaChi`, deriving the convergence, triple integrability,
kernel-translate membership, quotient-product integrability, compatible quotient measure and
nonzero level mass. The diagonal integrability (from VIII.3.2) is the named open prerequisite
`RationalLevelKernelDiagonalIntegrable`; the weight estimates and unimodularity are explicit
hypotheses.
-/

noncomputable section

open MeasureTheory Langlands.QuotientIntegration
open scoped ComplexConjugate ENNReal

namespace Langlands.HarishChandraSchwartz

universe u uG

section Generic

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  {A : Subgroup G} (hA : IsClosed (A : Set G))
  [MeasurableSpace A] [BorelSpace A]
  [MeasurableSpace (LeftQuotient A)] [BorelSpace (LeftQuotient A)]
  {μA : Measure A} [SFinite μA] [μA.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μA]
  {μG : Measure G} [IsFiniteMeasureOnCompacts μG] {ν : Measure (LeftQuotient A)}
  {χ : A →* ℂˣ} {H : Subgroup G} {μH : Measure H} {E : G → ℂ} {Ξ σ : G → ℝ}

include hA in
/-- **The local kernel step of VIII.4.1, generic form.** Let `W` be a submodule of a
Schwartz space on which every central integral converges. Suppose every `φ ∈ W` is left
`H`-invariant, satisfies `φ * E = mes(H) φ`, and has absolutely convergent triple integrals.
Suppose also that every kernel translate `α_χ(·, y)` is the central integral of an element of
`W`, that the quotient products are integrable, and that the diagonal of `α_χ` is integrable.
Then the span of the central integrals of `W` is finite dimensional. -/
theorem finiteDimensional_schwartzCentralIntegralSpan_of_kernel [MeasurableMul A] [SFinite μG]
    [SFinite μH] [MeasurableInv A] [μA.IsInvInvariant] (hν : IsCompatible A μG μA ν)
    (hAc : A ≤ Subgroup.center G) (hχ : IsUnitaryCharacter χ) (hE : ∀ x, conj (E x) = E x)
    (hmes : (μH Set.univ).toReal ≠ 0) {W : Submodule ℂ (Space Ξ σ)}
    (hconv : CentralIntegralConvergesOn W μA χ)
    (hinv : ∀ φ ∈ W, ∀ h ∈ H, ∀ x, (φ : G → ℂ) (h * x) = (φ : G → ℂ) x)
    (hrep : ∀ φ ∈ W, ∀ x,
      convolution μG (φ : G → ℂ) E x = (μH Set.univ).toReal * (φ : G → ℂ) x)
    (htriple : ∀ φ ∈ W, ∀ g, Integrable
      (fun p : G × A × H => E (p.1⁻¹ * p.2.2 * ((p.2.1 : G) * g)) * (φ : G → ℂ) p.1)
      (μG.prod (μA.prod μH)))
    (hKW : ∀ y, ∃ ψ ∈ W,
      centralProjection μA χ (ψ : G → ℂ) = fun g => kernelAlphaChi μA χ μH E g y)
    (hprod : ∀ φ ∈ W, ∀ φ' ∈ W, Integrable (fun q : LeftQuotient A =>
      centralProjection μA χ (φ : G → ℂ) q.out *
        conj (centralProjection μA χ (φ' : G → ℂ) q.out)) ν)
    (hdiag : Integrable (fun q : LeftQuotient A => (kernelAlphaChi μA χ μH E q.out q.out).re) ν) :
    FiniteDimensional ℂ (schwartzCentralIntegralSpan W μA χ) := by
  have himg := coe_schwartzCentralIntegralSpan_eq_image W μA χ hconv
  have hmem : ∀ f, f ∈ schwartzCentralIntegralSpan W μA χ ↔
      ∃ φ : Space Ξ σ, φ ∈ W ∧ centralProjection μA χ (φ : G → ℂ) = f := by
    intro f
    rw [← SetLike.mem_coe, himg]
    rfl
  refine finiteDimensional_of_kernelAlphaChi hA hν hAc hχ hE hmes ?_ ?_ ?_ hdiag
  · intro f hf
    obtain ⟨φ, hφ, rfl⟩ := (hmem f).1 hf
    exact ⟨φ, rfl, hinv φ hφ, hrep φ hφ, htriple φ hφ⟩
  · intro y
    obtain ⟨ψ, hψ, heq⟩ := hKW y
    exact (hmem _).2 ⟨ψ, hψ, heq⟩
  · intro f hf f' hf'
    obtain ⟨φ, hφ, rfl⟩ := (hmem f).1 hf
    obtain ⟨φ', hφ', rfl⟩ := (hmem f').1 hf'
    exact hprod φ hφ φ' hφ'

end Generic

section Triple

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
  {μG : Measure G} [μG.IsMulLeftInvariant] [SFinite μG]
  {K : Subgroup G} [CompactSpace K] {Ξ σ : G → ℝ}
  {A : Subgroup G} [MeasurableSpace A] [BorelSpace A] {μA : Measure A} [SFinite μA]
  {H : Subgroup G} [MeasurableSpace H] [BorelSpace H] {μH : Measure H} [IsFiniteMeasure μH]

/-- **Absolute convergence of the triple integral** in the proof of VIII.4.1. Let `E` and `φ`
be continuous with all `ν_r` finite, and let `φ` be left `H`-invariant. Then
`(g', a, h) ↦ E(g'⁻¹ h a g) φ(g')` is integrable on `G × A × H`. The substitution `g' ↦ h g'`
removes `h`. The integral over `G` is bounded by the convolution estimate of Lemma III.6.1,
and the integral over `A` by the central weights. -/
theorem integrable_kernelTriple (hcw : ConvolutionWeights μG K Ξ σ)
    (hw : CentralWeights μA Ξ σ) {E φ : G → ℂ} (hEc : Continuous E) (hφc : Continuous φ)
    (hEν : ∀ r, nu Ξ σ r E < ⊤) (hφν : ∀ r, nu Ξ σ r φ < ⊤)
    (hφH : ∀ h ∈ H, ∀ x, φ (h * x) = φ x) (g : G) :
    Integrable (fun p : G × A × H => E (p.1⁻¹ * p.2.2 * ((p.2.1 : G) * g)) * φ p.1)
      (μG.prod (μA.prod μH)) := by
  obtain ⟨s, hs, hsI⟩ := hw.exists_lintegral_lt_top
  set d : ℝ := (hcw.squareExponent : ℝ) with hd
  set C : ℝ≥0∞ := nu Ξ σ (s + d) φ * nu Ξ σ s E * ENNReal.ofReal (Ξ g * (1 + σ g) ^ s) *
      ∫⁻ x, ENNReal.ofReal (Ξ x ^ 2 * (1 + σ x) ^ (-d)) ∂μG with hC
  have hCtop : C < ⊤ :=
    ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.mul_lt_top (hφν _) (hEν _))
      ENNReal.ofReal_lt_top) hcw.lintegral_square_lt_top
  have hmeas : Measurable
      (fun p : G × A × H => E (p.1⁻¹ * p.2.2 * ((p.2.1 : G) * g)) * φ p.1) :=
    (hEc.measurable.comp ((measurable_fst.inv.mul (continuous_subtype_val.measurable.comp
      (measurable_snd.comp measurable_snd))).mul ((continuous_subtype_val.measurable.comp
        (measurable_fst.comp measurable_snd)).mul measurable_const))).mul
      (hφc.measurable.comp measurable_fst)
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  have hσm : Measurable fun q : A × H => ENNReal.ofReal ((1 + σ q.1) ^ (-s)) :=
    ENNReal.measurable_ofReal.comp ((measurable_const.add
      (hcw.continuous_sigma.measurable.comp (continuous_subtype_val.measurable.comp
        measurable_fst))).pow_const (-s))
  have hinner : ∀ q : A × H,
      ∫⁻ x, ‖E (x⁻¹ * q.2 * ((q.1 : G) * g)) * φ x‖ₑ ∂μG ≤
        C * ENNReal.ofReal ((1 + σ q.1) ^ (-s)) := by
    rintro ⟨a, h⟩
    have hshift := (lintegral_mul_left_eq_self
      (fun x => ‖E (x⁻¹ * h * ((a : G) * g)) * φ x‖ₑ) (h : G) (μ := μG)).symm
    rw [hshift]
    have hpt : ∀ x : G, ‖E ((h * x)⁻¹ * h * ((a : G) * g)) * φ (h * x)‖ₑ =
        ‖φ x‖ₑ * ‖E (x⁻¹ * ((a : G) * g))‖ₑ := by
      intro x
      rw [hφH h h.2 x, enorm_mul, mul_comm]
      congr 3
      group
    simp_rw [hpt]
    refine (hcw.lintegral_enorm_mul_le hs (s + d) φ E ((a : G) * g)).trans ?_
    rw [show s - (s + d) = -d by ring, hw.xi_mul]
    have hbd : ENNReal.ofReal (Ξ g * (1 + σ ((a : G) * g)) ^ (-s)) ≤
        ENNReal.ofReal (Ξ g * (1 + σ g) ^ s) * ENNReal.ofReal ((1 + σ a) ^ (-s)) := by
      rw [← ENNReal.ofReal_mul (mul_nonneg (hw.pos g).le
        (Real.rpow_nonneg (by linarith [hw.nonneg g]) _))]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (hw.rpow_neg_le hs a g) (hw.pos g).le
    calc nu Ξ σ (s + d) φ * nu Ξ σ s E * ENNReal.ofReal (Ξ g * (1 + σ ((a : G) * g)) ^ (-s)) *
          ∫⁻ x, ENNReal.ofReal (Ξ x ^ 2 * (1 + σ x) ^ (-d)) ∂μG
        ≤ nu Ξ σ (s + d) φ * nu Ξ σ s E *
            (ENNReal.ofReal (Ξ g * (1 + σ g) ^ s) * ENNReal.ofReal ((1 + σ a) ^ (-s))) *
          ∫⁻ x, ENNReal.ofReal (Ξ x ^ 2 * (1 + σ x) ^ (-d)) ∂μG := by gcongr
      _ = C * ENNReal.ofReal ((1 + σ a) ^ (-s)) := by rw [hC]; ring
  calc ∫⁻ p, ‖E (p.1⁻¹ * p.2.2 * ((p.2.1 : G) * g)) * φ p.1‖ₑ ∂(μG.prod (μA.prod μH))
      = ∫⁻ q, ∫⁻ x, ‖E (x⁻¹ * q.2 * ((q.1 : G) * g)) * φ x‖ₑ ∂μG ∂(μA.prod μH) :=
        lintegral_prod_symm _ hmeas.enorm.aemeasurable
    _ ≤ ∫⁻ q, C * ENNReal.ofReal ((1 + σ q.1) ^ (-s)) ∂(μA.prod μH) := lintegral_mono hinner
    _ = C * ((∫⁻ a, ENNReal.ofReal ((1 + σ a) ^ (-s)) ∂μA) * μH Set.univ) := by
        rw [lintegral_const_mul' _ _ hCtop.ne,
          lintegral_prod (fun q : A × H => ENNReal.ofReal ((1 + σ q.1) ^ (-s)))
            hσm.aemeasurable]
        simp only [lintegral_const, lintegral_mul_const' _ _ (measure_ne_top μH Set.univ)]
    _ < ⊤ := ENNReal.mul_lt_top hCtop (ENNReal.mul_lt_top hsI (measure_lt_top μH Set.univ))

end Triple

section KernelTranslate

/-- The integral of a locally constant family of functions over a compact space with a finite
measure is a finite linear combination of members of the family. -/
theorem integral_apply_eq_sum_of_isLocallyConstant {X Y : Type*} [TopologicalSpace X]
    [CompactSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] {μ : Measure X}
    [IsFiniteMeasure μ] {F : X → Y → ℂ} (hF : IsLocallyConstant F) (w : Y) :
    ∫ x, F x w ∂μ = ∑ c ∈ hF.range_finite.toFinset, (μ.real (F ⁻¹' {c}) : ℂ) * c w := by
  classical
  have hmeas : ∀ c, MeasurableSet (F ⁻¹' {c}) := fun c => (hF.isOpen_fiber c).measurableSet
  have hpt : ∀ x, F x w =
      ∑ c ∈ hF.range_finite.toFinset, (F ⁻¹' {c}).indicator (fun _ => c w) x := by
    intro x
    rw [Finset.sum_eq_single (F x)]
    · simp
    · intro c _ hc
      simp [Ne.symm hc]
    · intro hx
      exact absurd (by simp) hx
  simp_rw [hpt]
  rw [integral_finsetSum _ (fun c _ => (integrable_const (c w)).indicator (hmeas c))]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [integral_indicator_const _ (hmeas c), Complex.real_smul]

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {Ξ σ : G → ℝ}
  {H : Subgroup G}

/-- If `E` is right `H`-invariant and `H` is open, then `h ↦ (g ↦ E(g⁻¹ h y))` is locally
constant on `H`: it does not change under right multiplication by `H ∩ y H y⁻¹`. -/
theorem isLocallyConstant_kernelIntegrand (hHo : IsOpen (H : Set G)) {E : G → ℂ}
    (hE : ∀ k ∈ H, ∀ x, E (x * k) = E x) (y : G) :
    IsLocallyConstant (fun (h : H) (g : G) => E (g⁻¹ * h * y)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro h
  have hopen : IsOpen {h' : H | y⁻¹ * ((h : G)⁻¹ * h') * y ∈ H} :=
    hHo.preimage ((continuous_const.mul (continuous_const.mul continuous_subtype_val)).mul
      continuous_const)
  filter_upwards [hopen.mem_nhds (by simp [H.one_mem])] with h' hh'
  funext g
  have e : g⁻¹ * (h' : G) * y = g⁻¹ * h * y * (y⁻¹ * ((h : G)⁻¹ * h') * y) := by group
  rw [e, hE _ hh']

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- A function bi-invariant under `H` stays bi-invariant after averaging `g ↦ E(g⁻¹ h y)`
over `H` with a left-invariant measure. -/
theorem isBiInvariant_integral_kernel [MeasurableSpace H] [MeasurableMul H] {μH : Measure H}
    [μH.IsMulLeftInvariant] {E : G → ℂ} (hE : IsBiInvariant H E) (y : G) :
    IsBiInvariant H (fun g => ∫ h, E (g⁻¹ * h * y) ∂μH) := by
  intro k₁ hk₁ k₂ hk₂ g
  have h1 : ∀ h : H, E ((k₁ * g * k₂)⁻¹ * h * y) =
      E (g⁻¹ * (((⟨k₁, hk₁⟩ : H)⁻¹ * h : H) : G) * y) := by
    intro h
    have e : (k₁ * g * k₂)⁻¹ * h * y =
        k₂⁻¹ * (g⁻¹ * (((⟨k₁, hk₁⟩ : H)⁻¹ * h : H) : G) * y) * 1 := by
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
      group
    rw [e, hE _ (H.inv_mem hk₂) _ H.one_mem]
  simp_rw [h1]
  exact integral_mul_left_eq_self (fun h : H => E (g⁻¹ * (h : G) * y)) _

variable [MeasurableSpace H] [OpensMeasurableSpace H] [CompactSpace H] {μH : Measure H}
  [IsFiniteMeasure μH]

/-- **The kernel translates lie in a translation-stable submodule.** Let `S` be a submodule of
the Schwartz space stable under left translations, and let `E ∈ S` be invariant under
`x ↦ x⁻¹` and right invariant under the open compact `H`. Then `g ↦ ∫_H E(g⁻¹ h y) dμ_H` is
an element of `S`: it is a finite combination of left translates of `E`. -/
theorem exists_mem_eq_integral_kernel (hHo : IsOpen (H : Set G))
    (hTW : TranslationWeights Ξ σ) {S : Submodule ℂ (Space Ξ σ)}
    (hS : ∀ f ∈ S, ∀ g, Space.translate hTW 1 g f ∈ S) {E : Space Ξ σ} (hES : E ∈ S)
    (hEinv : ∀ x, (E : G → ℂ) x⁻¹ = (E : G → ℂ) x)
    (hEH : ∀ k ∈ H, ∀ x, (E : G → ℂ) (x * k) = (E : G → ℂ) x) (y : G) :
    ∃ ψ ∈ S, (ψ : G → ℂ) = fun g => ∫ h, (E : G → ℂ) (g⁻¹ * h * y) ∂μH := by
  classical
  set F : H → G → ℂ := fun h g => (E : G → ℂ) (g⁻¹ * h * y) with hFdef
  have hF : IsLocallyConstant F := isLocallyConstant_kernelIntegrand hHo hEH y
  let rep : (G → ℂ) → H := Function.invFun F
  have hrep : ∀ c ∈ hF.range_finite.toFinset, F (rep c) = c := by
    intro c hc
    exact Function.invFun_eq (by simpa using hc)
  refine ⟨∑ c ∈ hF.range_finite.toFinset,
    (μH.real (F ⁻¹' {c}) : ℂ) • Space.translate hTW 1 ((rep c : G) * y) E, ?_, ?_⟩
  · exact S.sum_mem fun c _ => S.smul_mem _ (hS E hES _)
  · funext g
    rw [integral_apply_eq_sum_of_isLocallyConstant hF g]
    have hcoe := congrFun (map_sum (Space.toFunLinear (Ξ := Ξ) (σ := σ)) (fun c =>
      (μH.real (F ⁻¹' {c}) : ℂ) • Space.translate hTW 1 ((rep c : G) * y) E)
        hF.range_finite.toFinset) g
    simp only [Space.toFunLinear_apply] at hcoe
    rw [hcoe, Finset.sum_apply]
    refine Finset.sum_congr rfl fun c hc => ?_
    have hcg : c g = F (rep c) g := by rw [hrep c hc]
    rw [hcg]
    simp only [Space.coe_smul, Pi.smul_apply, smul_eq_mul, Space.coe_translate, translate_apply,
      hFdef]
    congr 1
    rw [← hEinv]
    congr 1
    group

end KernelTranslate

section Space

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Nonempty (CompactOpenSubgroup G)] {Ξ σ : G → ℝ}

/-- Every element of the Schwartz space is continuous and has all `ν_r` finite. -/
theorem Space.continuous_and_nu_lt_top (f : Space Ξ σ) :
    Continuous (f : G → ℂ) ∧ ∀ r, nu Ξ σ r (f : G → ℂ) < ⊤ := by
  obtain ⟨H, hH⟩ := (mem_schwartzSubmodule_iff Ξ σ).mp (Space.coe_mem f)
  exact ⟨continuous_of_mem_levelSubmodule hH, hH.2⟩

end Space

section Central

variable {Γ : Type uG} [Group Γ] {A : Subgroup Γ}

/-- On a central subgroup, right and left multiplication agree. -/
theorem mul_comm_of_le_center (hAc : A ≤ Subgroup.center Γ) (x y : A) : x * y = y * x :=
  Subtype.ext ((Subgroup.mem_center_iff.mp (hAc y.2) x))

/-- A left-invariant measure on a central subgroup is right invariant. -/
theorem isMulRightInvariant_of_le_center [MeasurableSpace A] (hAc : A ≤ Subgroup.center Γ)
    (μ : Measure A) [μ.IsMulLeftInvariant] : μ.IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  have h : (fun x : A => x * g) = fun x => g * x := funext fun x => mul_comm_of_le_center hAc x g
  rw [h]
  exact map_mul_left_eq_self μ g

/-- A regular Haar measure on a central subgroup is invariant under inversion. -/
theorem isInvInvariant_of_le_center [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [MeasurableSpace A] [BorelSpace A] [LocallyCompactSpace A] (hAc : A ≤ Subgroup.center Γ)
    (μ : Measure A) [μ.IsHaarMeasure] [μ.Regular] : μ.IsInvInvariant := by
  let : CommGroup A := { (inferInstance : Group A) with mul_comm := mul_comm_of_le_center hAc }
  exact Measure.IsHaarMeasure.isInvInvariant_of_regular μ

end Central

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open Langlands.Aubert.General

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

section Rational

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S} {s : T.toGrp ⟶ G}
  {K : OpenSubgroup (rationalPoints G)}
  (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) (K : Subgroup (rationalPoints G)))
  {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N))

/-- **The properties of Waldspurger's function `°e_H` used in the kernel step of VIII.4.1.**
Here `E` is an element of the actual rational Schwartz space, `H` a compact open subgroup and
`muG` a measure on `G(F)`, in practice a Haar measure. The fields are:
`E` lies in the cuspidal level `°C_H`; `E` is real; `E(x⁻¹) = E(x)`; `E` vanishes outside
`G¹`; and `φ * E = mes(H) φ` for every `φ ∈ °C_H`, with `mes(H) = muG(H)`. -/
structure IsRationalCuspidalLevelKernel (muG : Measure (rationalPoints G))
    (H : OpenSubgroup (rationalPoints G)) (E : RationalSchwartzSpace hKc hPK ρ) : Prop where
  mem_level : E ∈ rationalCuspidalLevel hKc hPK ρ H.toSubgroup
  conj_eq : ∀ x, conj ((E : rationalPoints G → ℂ) x) = (E : rationalPoints G → ℂ) x
  inv_eq : ∀ x, (E : rationalPoints G → ℂ) x⁻¹ = (E : rationalPoints G → ℂ) x
  eq_zero_of_not_mem : ∀ x, x ∉ rationalCommonNormKernel G → (E : rationalPoints G → ℂ) x = 0
  convolution_eq : ∀ φ ∈ rationalCuspidalLevel hKc hPK ρ H.toSubgroup, ∀ x,
    convolution muG (φ : rationalPoints G → ℂ) (E : rationalPoints G → ℂ) x =
      (muG (H : Set (rationalPoints G))).toReal * (φ : rationalPoints G → ℂ) x

/-- The measure `μ_H` on `H` used in the kernel `α`: the restriction of `muG`. -/
abbrev levelMeasure (muG : Measure (rationalPoints G)) (H : OpenSubgroup (rationalPoints G)) :
    Measure H :=
  muG.comap H.toSubgroup.subtype

/-- **The diagonal input of VIII.4.1** (from VIII.3.2): for every compatible quotient measure on
`A_G(F) \ G(F)`, the real part of the diagonal `q ↦ α_χ(q̇, q̇)` of the kernel built from `E`
is integrable. This is a named open prerequisite of the kernel step. -/
def RationalLevelKernelDiagonalIntegrable (muA : Measure (rationalPoints.map s).range)
    (χ : (rationalPoints.map s).range →* ℂˣ)
    (muG : Measure (rationalPoints G)) (H : OpenSubgroup (rationalPoints G))
    (E : RationalSchwartzSpace hKc hPK ρ) : Prop :=
  ∀ [muA.IsMulRightInvariant] [MeasurableSpace (LeftQuotient (rationalPoints.map s).range)]
    [BorelSpace (LeftQuotient (rationalPoints.map s).range)]
    (muQ : Measure (LeftQuotient (rationalPoints.map s).range)),
    IsCompatible (rationalPoints.map s).range muG muA muQ →
    Integrable (fun q : LeftQuotient (rationalPoints.map s).range =>
      (kernelAlphaChi muA χ (levelMeasure muG H) (E : rationalPoints G → ℂ)
        q.out q.out).re) muQ

/-- Left and right translates preserve the actual cuspidal subspace. -/
theorem translate_mem_rationalCuspidalSubmodule
    (hTW : TranslationWeights (rationalXi hKc hPK) (rationalHeight (F := F) ρ))
    {f : RationalSchwartzSpace hKc hPK ρ} (hf : f ∈ rationalCuspidalSubmodule hKc hPK ρ)
    (g₁ g₂ : rationalPoints G) :
    Space.translate hTW g₁ g₂ f ∈ rationalCuspidalSubmodule hKc hPK ρ :=
  fun I hI muU hmuU => (hf I hI muU hmuU).translate g₁ g₂

local instance rationalKernelStepSecondCountable : SecondCountableTopology (rationalPoints G) :=
  rationalPoint_secondCountableTopology F G
local instance rationalKernelStepT2 : T2Space (rationalPoints G) := rationalPoint_t2Space F G

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
/-- `μ_H(H) = muG(H)`. -/
theorem levelMeasure_univ (muG : Measure (rationalPoints G))
    (H : OpenSubgroup (rationalPoints G)) :
    levelMeasure muG H Set.univ = muG (H : Set (rationalPoints G)) := by
  have hme : MeasurableEmbedding (H.toSubgroup.subtype : H.toSubgroup → rationalPoints G) :=
    MeasurableEmbedding.subtype_coe H.isOpen.measurableSet
  rw [levelMeasure, hme.comap_apply, Set.image_univ]
  simp

instance levelMeasure_isMulLeftInvariant (muG : Measure (rationalPoints G))
    [muG.IsMulLeftInvariant] (H : OpenSubgroup (rationalPoints G)) :
    (levelMeasure muG H).IsMulLeftInvariant := by
  have : BorelSpace H.toSubgroup := Subtype.borelSpace _
  have : MeasurableMul H.toSubgroup :=
    ⟨fun c => (continuous_const.mul continuous_id).measurable,
      fun c => (continuous_id.mul continuous_const).measurable⟩
  exact Measure.IsMulLeftInvariant.comap muG
    (MeasurableEmbedding.subtype_coe H.isOpen.measurableSet)

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
/-- For a Haar measure and a compact open `H`, `0 < muG(H) < ∞`, so `mes(H) ≠ 0`. -/
theorem levelMeasure_univ_toReal_ne_zero (muG : Measure (rationalPoints G)) [muG.IsHaarMeasure]
    (H : OpenSubgroup (rationalPoints G)) (hHc : IsCompact (H : Set (rationalPoints G))) :
    (levelMeasure muG H Set.univ).toReal ≠ 0 := by
  rw [levelMeasure_univ]
  exact ENNReal.toReal_ne_zero.mpr ⟨(H.isOpen.measure_pos muG ⟨1, H.one_mem⟩).ne',
    hHc.measure_lt_top.ne⟩

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
theorem levelMeasure_isFiniteMeasure (muG : Measure (rationalPoints G)) [muG.IsHaarMeasure]
    (H : OpenSubgroup (rationalPoints G)) (hHc : IsCompact (H : Set (rationalPoints G))) :
    IsFiniteMeasure (levelMeasure muG H) :=
  ⟨by rw [levelMeasure_univ]; exact hHc.measure_lt_top⟩

/-- **Unimodularity of `G(F)`**: for connected reductive `G`, every Haar measure on `G(F)` is
right invariant. The modular character is trivial (`rationalPoints_modularCharacter_eq_one`, from
the Library's `rationalReductiveUnimodularity` with the proved `standardCocharacter`), and
`map (· * g) μ = Δ(g) μ` (`Measure.map_right_mul_eq_modularCharacterFun_smul`). -/
theorem rationalHaar_isMulRightInvariant (hG : IsConnectedReductive G)
    (muG : Measure (rationalPoints G)) [muG.IsHaarMeasure] : muG.IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  have h := Measure.map_right_mul_eq_modularCharacterFun_smul muG g
  have h1 : Measure.modularCharacterFun g = 1 := rationalPoints_modularCharacter_eq_one hG g
  rw [h, h1, one_smul]

/-- **The local kernel step of VIII.4.1 on actual rational points.** Let `H` be a compact open
subgroup, `muG` a two-sided Haar measure on `G(F)`, `muA` a Haar measure on `A_G(F)` and `χ` a
unitary character. Let `E` have the properties of `°e_H` (`IsRationalCuspidalLevelKernel`).
Assume the central weights, the `L²` weights and the convolution weights of the actual `Ξ`
and `σ`, and the diagonal input. Then the actual central level span is finite dimensional. -/
theorem IsRationalCuspidalLevelKernel.finiteDimensional_levelSpan (hs : IsSplitComponent s)
    (muA : Measure (rationalPoints.map s).range) [muA.IsHaarMeasure]
    (χ : (rationalPoints.map s).range →* ℂˣ) (hχ : IsUnitaryCharacter χ)
    (muG : Measure (rationalPoints G)) [muG.IsHaarMeasure] [muG.IsMulRightInvariant]
    (H : OpenSubgroup (rationalPoints G)) (hHc : IsCompact (H : Set (rationalPoints G)))
    {E : RationalSchwartzSpace hKc hPK ρ} (hE : IsRationalCuspidalLevelKernel hKc hPK ρ muG H E)
    (hw : CentralWeights muA (rationalXi hKc hPK) (rationalHeight (F := F) ρ))
    (hL : L2Weights muG (rationalXi hKc hPK) (rationalHeight (F := F) ρ))
    {K' : Subgroup (rationalPoints G)} [CompactSpace K']
    (hcw : ConvolutionWeights muG K' (rationalXi hKc hPK) (rationalHeight (F := F) ρ))
    (hdiag : RationalLevelKernelDiagonalIntegrable hKc hPK ρ muA χ muG H E) :
    FiniteDimensional ℂ (rationalCuspidalCentralLevelSpan hKc hPK ρ muA χ H.toSubgroup) := by
  have hA : IsClosed ((rationalPoints.map s).range : Set (rationalPoints G)) :=
    isClosed_range_splitComponent G s hs
  have hAc : (rationalPoints.map s).range ≤ Subgroup.center (rationalPoints G) :=
    hs.isCentralSplitTorus.isCentral.range_le_center
  have : CompactSpace H := isCompact_iff_compactSpace.mp hHc
  have : LocallyCompactSpace (rationalPoints.map s).range :=
    hA.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology (rationalPoints.map s).range :=
    inferInstanceAs (SecondCountableTopology
      ((rationalPoints.map s).range : Set (rationalPoints G)))
  have : muA.IsMulRightInvariant := isMulRightInvariant_of_le_center hAc muA
  have : muA.IsInvInvariant := isInvInvariant_of_le_center hAc muA
  have : (levelMeasure muG H).IsMulLeftInvariant := levelMeasure_isMulLeftInvariant muG H
  have : IsFiniteMeasure (levelMeasure muG H) := levelMeasure_isFiniteMeasure muG H hHc
  have : Nonempty (CompactOpenSubgroup (rationalPoints G)) := ⟨⟨K, hKc⟩⟩
  let : MeasurableSpace (LeftQuotient (rationalPoints.map s).range) := borel _
  have : BorelSpace (LeftQuotient (rationalPoints.map s).range) := ⟨rfl⟩
  obtain ⟨muQ, hQ⟩ := @compatibleMeasureExists (rationalPoints G) _ _ _ _ _ _ _
    (rationalPoints.map s).range hA _ _ muG muA _ _ _ _ _ _ _ _
  have hTW := rationalTranslationWeights K.isOpen hKc hPK ρ
  have hmes := levelMeasure_univ_toReal_ne_zero muG H hHc
  have hW : ∀ φ ∈ rationalCuspidalLevel hKc hPK ρ H.toSubgroup,
      ∀ h ∈ H.toSubgroup, ∀ x, (φ : rationalPoints G → ℂ) (h * x) = φ x := by
    intro φ hφ h hh x
    simpa using hφ.2 h hh 1 H.one_mem x
  refine finiteDimensional_schwartzCentralIntegralSpan_of_kernel hA hQ hAc hχ hE.conj_eq hmes
    (CentralWeights.convergesOn _ muA χ hw hχ) hW ?_ ?_ ?_ ?_ (hdiag muQ hQ)
  · intro φ hφ x
    rw [hE.convolution_eq φ hφ x, levelMeasure_univ]
  · intro φ hφ g
    obtain ⟨hEc, hEν⟩ := Space.continuous_and_nu_lt_top E
    obtain ⟨hφc, hφν⟩ := Space.continuous_and_nu_lt_top φ
    exact integrable_kernelTriple hcw hw hEc hφc hEν hφν (hW φ hφ) g
  · intro y
    obtain ⟨ψ, hψS, hψ⟩ := exists_mem_eq_integral_kernel (μH := levelMeasure muG H) H.isOpen hTW
      (fun f hf g => translate_mem_rationalCuspidalSubmodule hKc hPK ρ hTW hf 1 g)
      hE.mem_level.1 hE.inv_eq (fun k hk x => by simpa using hE.mem_level.2 1 H.one_mem k hk x) y
    refine ⟨((((levelMeasure muG H Set.univ).toReal : ℂ)⁻¹) ^ 2) • ψ, ⟨?_, ?_⟩, ?_⟩
    · exact (rationalCuspidalSubmodule hKc hPK ρ).smul_mem _ hψS
    · rw [SetLike.mem_coe, Submodule.mem_comap, map_smul, Space.toFunLinear_apply, hψ]
      change IsBiInvariant H.toSubgroup _
      intro k₁ hk₁ k₂ hk₂ g
      have hb := isBiInvariant_integral_kernel (μH := levelMeasure muG H) hE.mem_level.2 y
        k₁ hk₁ k₂ hk₂ g
      simp only [Space.toFunLinear_apply] at hb
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [hb]
    · funext g
      simp only [kernelAlphaChi]
      congr 1
      funext g'
      simp only [Space.coe_smul, Pi.smul_apply, smul_eq_mul, hψ, kernelAlpha]
  · intro φ _ φ' _
    exact integrable_centralProjection_mul_conj_out hA hQ hAc hw hL hχ (Space.coe_mem φ)
      (Space.coe_mem φ')

/-- The local kernel step for connected reductive `G`, with the right invariance of `muG`
supplied by `rationalHaar_isMulRightInvariant`. -/
theorem IsRationalCuspidalLevelKernel.finiteDimensional_levelSpan_of_connectedReductive
    (hG : IsConnectedReductive G) (hs : IsSplitComponent s)
    (muA : Measure (rationalPoints.map s).range) [muA.IsHaarMeasure]
    (χ : (rationalPoints.map s).range →* ℂˣ) (hχ : IsUnitaryCharacter χ)
    (muG : Measure (rationalPoints G)) [muG.IsHaarMeasure]
    (H : OpenSubgroup (rationalPoints G)) (hHc : IsCompact (H : Set (rationalPoints G)))
    {E : RationalSchwartzSpace hKc hPK ρ} (hE : IsRationalCuspidalLevelKernel hKc hPK ρ muG H E)
    (hw : CentralWeights muA (rationalXi hKc hPK) (rationalHeight (F := F) ρ))
    (hL : L2Weights muG (rationalXi hKc hPK) (rationalHeight (F := F) ρ))
    {K' : Subgroup (rationalPoints G)} [CompactSpace K']
    (hcw : ConvolutionWeights muG K' (rationalXi hKc hPK) (rationalHeight (F := F) ρ))
    (hdiag : RationalLevelKernelDiagonalIntegrable hKc hPK ρ muA χ muG H E) :
    FiniteDimensional ℂ (rationalCuspidalCentralLevelSpan hKc hPK ρ muA χ H.toSubgroup) := by
  have := rationalHaar_isMulRightInvariant hG muG
  exact hE.finiteDimensional_levelSpan hKc hPK ρ hs muA χ hχ muG H hHc hw hL hcw hdiag

end Rational

end Langlands.HarishChandraSchwartz

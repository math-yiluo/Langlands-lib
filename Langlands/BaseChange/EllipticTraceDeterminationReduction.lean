import Langlands.BaseChange.EllipticTraceDeterminationStatement
import Langlands.BaseChange.CharacterLocalIntegrabilityStatement
import Langlands.BaseChange.CharacterLocalValueConjugation
import Langlands.BaseChange.RegularEllipticOpen
import Langlands.BaseChange.RegularSetOpenConull
import Langlands.BaseChange.OrdinaryWeylHaarLocalPushforwards
import Langlands.BaseChange.ConcordantIntegralComparison

/-!
# Elliptic determination of traces from local integrability of characters

For a nonarchimedean local field `F` of characteristic zero, the elliptic determination of
traces on `GL_n(F)` (`EllipticTraceDeterminationStatement`) follows from Harish-Chandra's
theorem that the character of an irreducible admissible representation is a locally integrable
function, locally constant near the regular semisimple elements
(`CharacterLocalIntegrabilityStatement`; Harish-Chandra 1999, Theorem 16.3):
`EllipticTraceDeterminationFromLocalIntegrabilityStatement` states the implication and
`ellipticTraceDeterminationFromLocalIntegrability` proves it, through the Library's ordinary
Weyl decomposition of integrals over the regular semisimple set (Henniart–Lemaire 2011, II.2.10,
formula (2)). Arthur–Clozel (1989, Chapter 1, proof of Lemma 2.12) use this passage, for
twisted characters, between the integral of a character against a function whose orbital
integrals vanish off the elliptic set and the values of the character on the elliptic set. See
the paired Markdown.
-/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory HarmonicAnalysis JacquetLanglands
open Langlands.QuotientIntegration Langlands.TraceFormula
open scoped BigOperators

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

/-- A function that is constant near `x` and integrates to zero against every test function
supported in an open neighbourhood `U` of `x` vanishes at `x`: test against the indicator of a
compact open neighbourhood of `x` inside `U` on which the function is constant. -/
theorem eq_zero_of_forall_integral_mul_eq_zero {X : Type*} [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [TotallyDisconnectedSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure] {Θ : X → ℂ} {x : X}
    (hΘ : ∀ᶠ y in nhds x, Θ y = Θ x) {U : Set X} (hU : IsOpen U) (hxU : x ∈ U)
    (h : ∀ φ : SchwartzBruhat X, Function.support φ ⊆ U → ∫ y, φ y * Θ y ∂μ = 0) :
    Θ x = 0 := by
  obtain ⟨W, hWc, hWo, hxW⟩ := eventually_nhds_iff.1 hΘ
  obtain ⟨K, hKc, hKo, hxK, hKU⟩ := exists_isCompact_isClopen_subset (hU.inter hWo) ⟨hxU, hxW⟩
  let φ := Hecke.TestFunction.characteristic hKo hKc
  have hsupp : Function.support (φ : X → ℂ) = K :=
    Hecke.TestFunction.support_characteristic hKo hKc
  have hφ := h φ (hsupp ▸ hKU.trans Set.inter_subset_left)
  have hint : ∫ y, φ y * Θ y ∂μ = ((μ K).toReal : ℂ) * Θ x := by
    have hpt : (fun y => φ y * Θ y) = K.indicator (fun _ => Θ x) := by
      funext y
      change K.indicator (fun _ => (1 : ℂ)) y * Θ y = K.indicator (fun _ => Θ x) y
      by_cases hy : y ∈ K
      · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, one_mul]
        exact hWc y (hKU hy).2
      · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, zero_mul]
    rw [hpt, integral_indicator_const _ hKo.isClosed.measurableSet, Measure.real, Complex.real_smul]
  have hpos : ((μ K).toReal : ℂ) ≠ 0 := by
    have h0 : 0 < μ K := hKo.isOpen.measure_pos μ ⟨x, hxK⟩
    exact Complex.ofReal_ne_zero.2 (ENNReal.toReal_pos h0.ne' hKc.measure_lt_top.ne).ne'
  rw [hint] at hφ
  exact (mul_eq_zero.1 hφ).resolve_left hpos

/-- Harish-Chandra's local integrability of characters (Harish-Chandra 1999, Theorem 16.3)
implies the elliptic determination of traces, through the Weyl integration formula
(Henniart–Lemaire 2011, II.2.10 (2)).
The field universe `u` and the universe `uV` of the representation spaces are the same in the
premise and in the conclusion; the universe `uI` of the index type occurs only in the
conclusion. -/
def EllipticTraceDeterminationFromLocalIntegrabilityStatement.{u, uI, uV} : Prop :=
  CharacterLocalIntegrabilityStatement.{u, uV} → EllipticTraceDeterminationStatement.{u, uI, uV}

/-- Proof of `EllipticTraceDeterminationFromLocalIntegrabilityStatement`. Let `Θ` be the
combination `∑ i, a i * Θ i` of the character functions. It vanishes at every regular elliptic
element, by `eq_zero_of_forall_integral_mul_eq_zero` on the open regular elliptic set. The trace
combination at `f` is `∫ f Θ`, which is the integral over the regular semisimple set; the
ordinary Weyl decomposition writes it as a sum over tori of integrals over their regular points
of orbital integrals of `f Θ`. At a regular point `t` the function `Θ` is constant on the
conjugacy class of `t`, so the orbital integral of `f Θ` is `Θ t` times the orbital integral of
`f`: the first factor vanishes when `t` is regular elliptic and the second otherwise. -/
theorem ellipticTraceDeterminationFromLocalIntegrability.{u, uI, uV} :
    EllipticTraceDeterminationFromLocalIntegrabilityStatement.{u, uI, uV} := by
  intro hloc F _ _ _ _ _ n _hn μ _ I _ V _ _ ρ hρ hirr a hell f hf
  classical
  let _ := LocalFieldTopology.generalLinear_t2Space F n
  let _ := LocalFieldTopology.generalLinear_locallyCompactSpace F n
  let _ := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F n
  let _ := LocalFieldTopology.generalLinear_secondCountableTopology F n
  let _ : MeasurableSpace (GeneralLinear n F) := borel _
  have _ : BorelSpace (GeneralLinear n F) := ⟨rfl⟩
  -- character functions
  choose Θ hΘ hΘloc using fun i => hloc F n (ρ i) (hρ i) (hirr i)
  let Θs : GeneralLinear n F → ℂ := fun x => ∑ i, a i * Θ i x
  have hint (φ : SchwartzBruhat (GeneralLinear n F)) (i : I) :
      Integrable (fun x => φ x * Θ i x) μ :=
    (hΘ i μ).1.integrable_smul_left_of_hasCompactSupport φ.locallyConstant.continuous
      φ.hasCompactSupport
  have hsum (φ : SchwartzBruhat (GeneralLinear n F)) :
      ∑ i, a i * Character.distribution μ (ρ i) (hρ i) φ = ∫ x, φ x * Θs x ∂μ := by
    have hterm (i : I) : a i * Character.distribution μ (ρ i) (hρ i) φ =
        ∫ x, a i * (φ x * Θ i x) ∂μ := by
      rw [(hΘ i μ).2 φ, integral_const_mul]
    rw [Finset.sum_congr rfl fun i _ => hterm i,
      ← integral_finsetSum _ fun i _ => (hint φ i).const_mul (a i)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [Θs, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  -- local constancy and conjugation invariance on the regular semisimple set
  have hΘsloc (g : GeneralLinear n F) (hg : IsRegularSemisimple g) :
      ∀ᶠ x in nhds g, Θs x = Θs g := by
    have h : ∀ᶠ x in nhds g, ∀ i, Θ i x = Θ i g :=
      Filter.eventually_all.2 fun i => hΘloc i g hg
    filter_upwards [h] with x hx
    simp only [Θs, hx]
  have hΘconj (t : GeneralLinear n F) (ht : IsRegularSemisimple t) (x : GeneralLinear n F)
      (hxt : IsRegularSemisimple (x⁻¹ * t * x)) : Θs (x⁻¹ * t * x) = Θs t := by
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    exact ((hΘ i).hasCharacterValue (hΘloc i _ hxt)).unique
      (((hΘ i).hasCharacterValue (hΘloc i t ht)).conjugate x)
  -- vanishing on the regular elliptic set
  have hΘsell (g : GeneralLinear n F) (hg : IsRegularElliptic g) : Θs g = 0 := by
    refine eq_zero_of_forall_integral_mul_eq_zero μ (hΘsloc g hg.isRegularSemisimple)
      (isOpen_regularElliptic F n) hg fun φ hφ => ?_
    rw [← hsum φ]
    exact hell φ fun x hx => hφ hx
  -- the Weyl decomposition of `∫ f Θ`
  rw [hsum f]
  let g : GeneralLinear n F → ℂ := fun x => f x * Θs x
  have hΘsli : LocallyIntegrable Θs μ :=
    locallyIntegrable_finsetSum Finset.univ fun i _ => (hΘ i μ).1.smul (a i)
  have hg : Integrable g μ :=
    hΘsli.integrable_smul_left_of_hasCompactSupport f.locallyConstant.continuous
      f.hasCompactSupport
  obtain ⟨S, hS⟩ := WeylTorus.exists_isRepresentativeSet F n
  choose μT hμTH hμTR νT hνT using fun T : WeylTorus F n => T.exists_ordinaryMeasures μ
  have hregOpen : IsOpen {g : GeneralLinear n F | IsRegularSemisimple g} :=
    (regularSemisimpleOpenConull F n).1
  have hregT (T : WeylTorus F n) : MeasurableSet T.regularPoints :=
    (hregOpen.preimage continuous_subtype_val).measurableSet
  have hordT (T : WeylTorus F n) : T.HasOrdinaryLocalPushforwards μ
      (T.weightedOrdinaryOrbitMeasure (νT T) ((μT T).comap Subtype.val)
        T.discriminantWeight) := by
    have := hμTH T
    have := hμTR T
    exact ordinaryWeylHaarLocalPushforwards F n μ T (μT T) (νT T) (hνT T)
  have hμTσ (T : WeylTorus F n) : SigmaFinite (μT T) := by
    have := hμTH T
    let _ : LocallyCompactSpace T.val := T.isClosed_val.locallyCompactSpace
    let _ : SecondCountableTopology T.val :=
      inferInstanceAs (SecondCountableTopology ↥(T.val : Set (GeneralLinear n F)))
    infer_instance
  have hνTSF (T : WeylTorus F n) : SFinite (νT T) := by
    let _ := leftQuotient_locallyCompactSpace T.val
    let _ : SecondCountableTopology (LeftQuotient T.val) :=
      _root_.Topology.IsOpenQuotientMap.secondCountableTopology
        (leftQuotient_isOpenQuotientMap T.val)
    have := (hνT T).regular
    infer_instance
  have hτSF (T : WeylTorus F n) :
      SFinite ((μT T).comap (Subtype.val : T.regularPoints → _)) := by
    have := hμTσ T
    have : SigmaFinite ((μT T).comap (Subtype.val : T.regularPoints → _)) :=
      SigmaFinite.of_map _ measurable_subtype_coe.aemeasurable
        (by rw [map_comap_subtype_coe (hregT T)]; infer_instance)
    infer_instance
  have hne (T : WeylTorus F n) (t : T.regularPoints) : weylDiscriminant t.val.val ≠ 0 := by
    obtain ⟨hunit, hdet⟩ := det_ordinaryWeylDifferential t.val.val t.property
    exact hdet ▸ hunit.ne_zero
  have hwm (T : WeylTorus F n) : Measurable T.discriminantWeight :=
    (T.isLocallyConstant_discriminantWeight (hne T)).continuous.measurable
  obtain ⟨-, -, -, hEq⟩ := ordinaryWeylIntegralDecomposition F n μ S hS
    (fun T => νT T.val) (fun T => (μT T.val).comap Subtype.val)
    (fun T => T.val.discriminantWeight) (fun T => hνTSF T.val) (fun T => hτSF T.val)
    (fun T => hwm T.val)
    (fun T => Filter.Eventually.of_forall fun t => T.val.discriminantWeight_pos t (hne T.val t))
    (fun T => hordT T.val) g hg.integrableOn
  have hFull : ∫ x, g x ∂μ = ∫ x in {g | IsRegularSemisimple g}, g x ∂μ := by
    refine (setIntegral_eq_integral_of_ae_compl_eq_zero ?_).symm
    have hnull := (regularSemisimpleOpenConull F n).2 μ
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with x hx hx'
    exact absurd (not_not.1 hx) hx'
  change ∫ x, g x ∂μ = 0
  rw [hFull, hEq]
  refine (tsum_congr fun T => ?_).trans tsum_zero
  refine (integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)).trans (integral_zero _ _)
  have := hμTH T.val
  have := hμTR T.val
  have hpt (q : LeftQuotient T.val.val) :
      g (T.val.ordinaryOrbitMap (q, t)) = Θs t.val.val * f (T.val.ordinaryOrbitMap (q, t)) := by
    induction q using Quotient.inductionOn with
    | h x =>
      have hreg := T.val.isRegularSemisimple_ordinaryOrbitMap (Quotient.mk _ x, t)
      change f (x⁻¹ * t.val.val * x) * Θs (x⁻¹ * t.val.val * x) =
        Θs t.val.val * f (x⁻¹ * t.val.val * x)
      rw [hΘconj t.val.val t.property x hreg, mul_comm]
  have hinner : ∫ q, g (T.val.ordinaryOrbitMap (q, t)) ∂νT T.val = 0 := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul]
    by_cases he : IsRegularElliptic t.val.val
    · rw [hΘsell _ he, zero_mul]
    · obtain ⟨μγ, h1, h2, νγ, hc, -, hγ⟩ :=
        T.val.exists_orbitalIntegral_eq μ (μT T.val) (νT T.val) (hνT T.val) t
      rw [← hγ f, hf t.val.val t.property he μγ νγ hc, mul_zero]
  change WeylTorus.ordinaryOrbitIntegrand T.val (νT T.val) T.val.discriminantWeight g t = 0
  rw [WeylTorus.ordinaryOrbitIntegrand, hinner, smul_zero, smul_zero]

end Langlands.BaseChange

import Langlands.BaseChange.CharacterFunction
import Langlands.BaseChange.CyclicAlgebraTopology
import Langlands.BaseChange.RegularSetOpenConull
import Langlands.BaseChange.TwistedCharacter.LinearIndependence
import Langlands.BaseChange.TwistedCharacterLocalIntegrabilityStatement
import Langlands.BaseChange.TwistedTraceRegularNonvanishingStatement

/-!
# σ-regular nonvanishing of twisted traces from local integrability

The twisted trace `φ ↦ tr(τ(φ) ∘ A)` of an irreducible admissible representation `τ` of
`GL_n(E)`, for a cyclic algebra `E` and an isomorphism `A` of `τ` onto `τ^σ`, is nonzero on
some Schwartz–Bruhat function supported in the σ-regular set, provided the twisted character
is represented by a locally integrable function that is locally constant near σ-regular
elements: `TwistedTraceRegularNonvanishingFromLocalIntegrabilityStatement` states that
`TwistedCharacterLocalIntegrabilityStatement` implies `TwistedTraceRegularNonvanishingStatement`,
and `twistedTraceRegularNonvanishingFromLocalIntegrability` proves it (Henniart–Lemaire 2011,
II.2.8; Arthur–Clozel 1989, Chapter 1, Proposition 2.2 and Lemma 6.3). See the paired Markdown.
-/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory HarmonicAnalysis Langlands.JacquetLanglands

universe u v uG uW

section Generic

variable {G : Type uG} [TopologicalSpace G] [T2Space G] [LocallyCompactSpace G]
  [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]

/-- If a distribution has a nonzero local value at a point `x` of an open set `R`, relative to a
measure that is finite on compact sets and positive on nonempty open sets, then it does not
vanish on the characteristic function of some compact open neighbourhood of `x` inside `R`. -/
theorem exists_support_subset_ne_zero_of_hasLocalValue {μ : Measure G}
    [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure] {D : Distribution G} {x : G} {c : ℂ}
    (h : HasLocalValue μ D x c) (hc : c ≠ 0) {R : Set G} (hR : IsOpen R) (hx : x ∈ R) :
    ∃ f : SchwartzBruhat G, Function.support f ⊆ R ∧ D f ≠ 0 := by
  obtain ⟨U, hU, hxU, hf⟩ := h
  obtain ⟨K, hKc, hKo, hxK, hKU⟩ := exists_isCompact_isClopen_subset (hU.inter hR) ⟨hxU, hx⟩
  let f := Hecke.TestFunction.characteristic hKo hKc
  have hsupp : Function.support (f : G → ℂ) = K :=
    Hecke.TestFunction.support_characteristic hKo hKc
  refine ⟨f, hsupp ▸ hKU.trans Set.inter_subset_right, ?_⟩
  rw [hf f (hsupp ▸ hKU.trans Set.inter_subset_left)]
  have hint : ∫ y, f y ∂μ = ((μ K).toReal : ℂ) := by
    change ∫ y, K.indicator (fun _ => (1 : ℂ)) y ∂μ = _
    rw [integral_indicator_const _ hKo.isClosed.measurableSet, Measure.real]
    simp
  have hpos : ((μ K).toReal : ℂ) ≠ 0 := by
    have h0 : 0 < μ K := hKo.isOpen.measure_pos μ ⟨x, hxK⟩
    exact Complex.ofReal_ne_zero.2 (ENNReal.toReal_pos h0.ne' hKc.measure_lt_top.ne).ne'
  rw [hint]
  exact mul_ne_zero hc hpos

end Generic

section GeneralLinear

variable {F : Type u} [Field F] [TopologicalSpace F]
  {E : Type v} [CommRing E] [Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]
  [IsModuleTopology F E] {n : ℕ}
  [T2Space (GeneralLinear n E)] [LocallyCompactSpace (GeneralLinear n E)]
  [TotallyDisconnectedSpace (GeneralLinear n E)]
  [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- The twisted trace of an irreducible admissible representation of `GL_n(E)` with a
σ-intertwiner takes the value `1` on some test function (Arthur–Clozel, Chapter 1, Lemma 6.3). -/
theorem exists_twistedDistribution_eq_one {σ : E ≃ₐ[F] E} {l : ℕ} (hE : IsCyclicAlgebra σ l)
    (μ : Measure (GeneralLinear n E)) [μ.IsHaarMeasure]
    (τ : Representation ℂ (GeneralLinear n E) W) (hτ : IsAdmissible τ) (hirr : τ.IsIrreducible)
    (A : SigmaIntertwiner σ n τ) :
    ∃ f : SchwartzBruhat (GeneralLinear n E), twistedDistribution μ τ hτ A.toLinearMap f = 1 := by
  have hiter : ∀ (N : ℕ) (g : GeneralLinear n E),
      (⇑(entrywiseAut σ n))^[N] g = entrywiseAut (σ ^ N) n g := by
    intro N g
    induction N with
    | zero => simp [entrywiseAut_one_apply]
    | succ N ih =>
      rw [Function.iterate_succ_apply', ih, pow_succ', entrywiseAut_mul_apply]
  have hθ := exists_compact_openSubgroup_symm_mem (entrywiseAut σ n)
    (continuous_entrywiseAut σ n) l hE.pos (by
      intro g
      rw [hiter, hE.pow_eq_one, entrywiseAut_one_apply])
  obtain ⟨f, hf⟩ := exists_twistedDistribution_test_values μ (entrywiseAut σ n) hθ
    (ι := Unit) (V := fun _ => W) (fun _ => τ) (fun _ => hτ) (fun _ => hirr)
    (fun i j hij => (hij (Subsingleton.elim i j)).elim) (fun _ => A.toLinearMap)
    (fun _ g => SigmaIntertwiner.comp_apply_eq A g) (fun _ => A.toLinearEquiv.injective)
    (fun _ => 1)
  exact ⟨f, hf ()⟩

end GeneralLinear

/-- Local integrability of twisted characters, with local constancy near σ-regular elements,
implies that twisted traces are detected by σ-regularly supported test functions
(Henniart–Lemaire 2011, II.2.8; Arthur–Clozel 1989, Chapter 1, Proposition 2.2 and Lemma 6.3).
The three universe parameters of the premise and of the conclusion agree. -/
def TwistedTraceRegularNonvanishingFromLocalIntegrabilityStatement : Prop :=
  TwistedCharacterLocalIntegrabilityStatement.{u, v, uW} →
    TwistedTraceRegularNonvanishingStatement.{u, v, uW}

/-- Proof of `TwistedTraceRegularNonvanishingFromLocalIntegrabilityStatement`: the twisted
character function is not almost everywhere zero, since the twisted trace takes the value `1`
somewhere; the σ-singular set is null, so the function is nonzero at a σ-regular `δ`, where it
is locally constant; the indicator of a small compact open neighbourhood of `δ` in the open
σ-regular set has nonzero twisted trace. -/
theorem twistedTraceRegularNonvanishingFromLocalIntegrability :
    TwistedTraceRegularNonvanishingFromLocalIntegrabilityStatement.{u, v, uW} := by
  intro h F _ _ _ _ _ E _ _ _ _ _ σ l n hE
  have : Module.Finite F E := hE.1
  have := generalLinear_t2Space_of_finite F E n
  have := generalLinear_locallyCompactSpace_of_finite F E n
  have := generalLinear_totallyDisconnectedSpace_of_finite F E n
  let _ : MeasurableSpace (GeneralLinear n E) := borel _
  have _ : BorelSpace (GeneralLinear n E) := ⟨rfl⟩
  intro W _ _ τ hτ hirr A μ _
  obtain ⟨Θ, hΘ, hloc⟩ := h F E σ l n hE τ hτ hirr A
  obtain ⟨hRopen, hRnull⟩ := sigmaRegularOpenConull F E σ l n hE
  obtain ⟨f₀, hf₀⟩ := exists_twistedDistribution_eq_one hE μ τ hτ hirr A
  have hex : ∃ δ, IsSigmaRegular σ l δ ∧ Θ δ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hae : Θ =ᵐ[μ] 0 := by
      rw [Filter.EventuallyEq, ae_iff]
      exact measure_mono_null (fun x hx hreg => hx (hcon x hreg)) (hRnull μ)
    have h₀ := (hΘ μ).2 f₀
    rw [hf₀, integral_eq_zero_of_ae (hae.mono fun x hx => by simp [hx])] at h₀
    exact one_ne_zero h₀
  obtain ⟨δ, hδ, hΘδ⟩ := hex
  obtain ⟨φ, hφR, hφ⟩ := exists_support_subset_ne_zero_of_hasLocalValue
    ((hΘ.hasTwistedCharacterValue (hloc δ hδ)) μ) hΘδ hRopen hδ
  exact ⟨φ, fun x hx => hφR hx, hφ⟩

end Langlands.BaseChange

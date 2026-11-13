import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Algebra.Nonarchimedean.Basic

/-! # Comparing a Haar measure with a transported Haar measure

For a topological group isomorphism `e : H' ≃ₜ* V` onto a closed subgroup `V` of a locally
compact, second countable, nonarchimedean group `G`, a Haar measure `haar` on `V` that gives the
same integrals as a Haar measure `haar'` on `H'` to all continuous compactly supported functions
on `G` is the image measure `haar'.map e`; conversely the image measure is a Haar measure with
this property.
-/

noncomputable section

open MeasureTheory Topology

namespace Langlands.Aubert.General.RepresentedParabolic

/-- A locally compact nonarchimedean group has a compact open subgroup. -/
theorem exists_isCompact_openSubgroup {G : Type*} [Group G] [TopologicalSpace G]
    [LocallyCompactSpace G] [NonarchimedeanGroup G] :
    ∃ K : OpenSubgroup G, IsCompact (K : Set G) := by
  obtain ⟨C, hCc, hC⟩ := exists_compact_mem_nhds (1 : G)
  obtain ⟨K, hK⟩ := NonarchimedeanGroup.is_nonarchimedean C hC
  exact ⟨K, hCc.of_isClosed_subset K.isClosed hK⟩

section Transport

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H]
  [BorelSpace H]
  {H' : Type*} [Group H'] [TopologicalSpace H'] [IsTopologicalGroup H'] [MeasurableSpace H']
  [BorelSpace H']

/-- In a locally compact second countable group, a Haar measure that agrees with the image of
a Haar measure under a topological group isomorphism on one nonempty compact open set is that
image measure. -/
theorem haar_eq_map_of_measure_eq [LocallyCompactSpace H] [SecondCountableTopology H]
    (e : H' ≃ₜ* H) (haar' : Measure H') [haar'.IsHaarMeasure] (haar : Measure H)
    [haar.IsHaarMeasure] {S : Set H} (hSo : IsOpen S) (hSc : IsCompact S) (hSne : S.Nonempty)
    (hS : haar S = haar'.map e S) : haar = haar'.map e := by
  have h := Measure.isMulLeftInvariant_eq_smul haar (haar'.map e)
  have h0 : haar'.map e S ≠ 0 := hSo.measure_ne_zero _ hSne
  have htop : haar'.map e S ≠ ⊤ := hSc.measure_lt_top.ne
  have hS' := congrArg (fun ν : Measure H => ν S) h
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at hS'
  rw [hS] at hS'
  have hc : (Measure.haarScalarFactor haar (haar'.map e) : ENNReal) = 1 := by
    have : (Measure.haarScalarFactor haar (haar'.map e) : ENNReal) * haar'.map e S =
        1 * haar'.map e S := by rw [one_mul]; exact hS'.symm
    exact (ENNReal.mul_left_inj h0 htop).1 this
  have hc' : Measure.haarScalarFactor haar (haar'.map e) = 1 := by exact_mod_cast hc
  rw [h, hc', one_smul]

omit [IsTopologicalGroup H] [IsTopologicalGroup H'] in
/-- The image of a Haar measure under a topological group isomorphism transports integrals. -/
theorem integral_map_continuousMulEquiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : H' ≃ₜ* H) (haar' : Measure H') (φ : H → E) :
    ∫ y, φ y ∂(haar'.map e) = ∫ x, φ (e x) ∂haar' :=
  integral_map_equiv e.toHomeomorph.toMeasurableEquiv φ

end Transport

section Closed

variable {G : Type*} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
  (V : Subgroup G) [MeasurableSpace V] [BorelSpace V]
  {H' : Type*} [Group H'] [TopologicalSpace H'] [IsTopologicalGroup H'] [MeasurableSpace H']
  [BorelSpace H']

/-- Existence: the image `haar'.map e` of a Haar measure is a Haar measure on `V` with
`∫ φ(e x) dhaar'(x) = ∫ φ d(haar'.map e)` for every `φ : G → ℂ`. -/
theorem map_isHaarMeasure_integral_eq (e : H' ≃ₜ* V) (haar' : Measure H')
    [haar'.IsHaarMeasure] :
    (haar'.map e).IsHaarMeasure ∧
      ∀ φ : G → ℂ, ∫ x, φ (e x) ∂haar' = ∫ x, φ x ∂(haar'.map e) :=
  ⟨inferInstance, fun φ => (integral_map_continuousMulEquiv e haar' fun x : V => φ x).symm⟩

variable [LocallyCompactSpace G] [SecondCountableTopology G]

/-- Uniqueness: on a closed subgroup `V` of a locally compact, second countable,
nonarchimedean group `G`, a Haar measure `haar` with `∫ φ(e x) dhaar'(x) = ∫ φ dhaar` for all
continuous compactly supported `φ : G → ℂ` is the image measure `haar'.map e`. -/
theorem haar_eq_map_of_integral_eq (hV : IsClosed (V : Set G)) (e : H' ≃ₜ* V)
    (haar' : Measure H') [haar'.IsHaarMeasure] (haar : Measure V) [haar.IsHaarMeasure]
    (h : ∀ φ : G → ℂ, Continuous φ → HasCompactSupport φ →
      ∫ x, φ (e x) ∂haar' = ∫ x, φ x ∂haar) :
    haar = haar'.map e := by
  have : LocallyCompactSpace V := hV.locallyCompactSpace
  have : SecondCountableTopology V := inferInstanceAs (SecondCountableTopology (V : Set G))
  obtain ⟨K, hK⟩ := exists_isCompact_openSubgroup (G := G)
  let φ : G → ℂ := (K : Set G).indicator fun _ => 1
  have hφc : Continuous φ := K.isClopen.continuous_indicator continuous_const
  have hφs : HasCompactSupport φ :=
    HasCompactSupport.intro hK fun x hx => Set.indicator_of_notMem hx _
  let S : Set V := Subtype.val ⁻¹' (K : Set G)
  have hSo : IsOpen S := K.isOpen.preimage continuous_subtype_val
  have hSc : IsCompact S :=
    hV.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  have hSne : S.Nonempty := ⟨1, K.one_mem⟩
  have hSm : MeasurableSet S := hSo.measurableSet
  have hφS : (fun x : V => φ x) = S.indicator fun _ => (1 : ℂ) := by
    funext x
    by_cases hx : (x : G) ∈ (K : Set G)
    · simp [φ, S, Set.indicator_of_mem, hx]
    · simp [φ, S, Set.indicator_of_notMem, hx]
  have hint := h φ hφc hφs
  rw [← integral_map_continuousMulEquiv e haar' (fun x : V => φ x), hφS,
    integral_indicator_const _ hSm, integral_indicator_const _ hSm] at hint
  have hreal : (haar'.map e).real S = haar.real S := by
    simpa using hint
  have hfin : haar S ≠ ⊤ := hSc.measure_lt_top.ne
  have hfin' : haar'.map e S ≠ ⊤ := hSc.measure_lt_top.ne
  refine haar_eq_map_of_measure_eq e haar' haar hSo hSc hSne ?_
  exact ((ENNReal.toReal_eq_toReal_iff' hfin hfin').1 hreal.symm)

end Closed

end Langlands.Aubert.General.RepresentedParabolic

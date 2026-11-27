import Langlands.BaseChange.TwistedCharacter.SemisimpleDescentPushforward
import Langlands.BaseChange.TwistedCharacter.OpenCoset
import Langlands.HarmonicAnalysis.Distribution.TensorProduct
import Langlands.HarmonicAnalysis.Distribution.PushforwardLocalDensity

/-! # Recovering a cyclic character density from the semisimple slice -/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory MeasureTheory.Measure HarmonicAnalysis Set Function _root_.Topology

section ProductDensity

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] [T2Space Y]
  [LocallyCompactSpace X] [LocallyCompactSpace Y] [SecondCountableTopology X]
  [SecondCountableTopology Y] [MeasurableSpace X] [MeasurableSpace Y]
  [BorelSpace X] [BorelSpace Y] (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
  (ξ : Measure Y) [SigmaFinite ξ] (θ : Y → ℂ) (hθ : Integrable θ ξ)

include hθ in
omit [T2Space X] [T2Space Y] [SecondCountableTopology Y] [BorelSpace X] [BorelSpace Y] in
private theorem locallyIntegrable_comp_snd_prod : LocallyIntegrable (θ ∘ Prod.snd) (μ.prod ξ) := by
  rw [locallyIntegrable_iff]
  intro K hK
  let J := Prod.fst '' K
  have hJ : IsCompact J := hK.image continuous_fst
  have hFin : IsFiniteMeasure (μ.restrict J) := ⟨by
    rw [Measure.restrict_apply_univ]; exact hJ.measure_lt_top⟩
  have h : IntegrableOn (θ ∘ Prod.snd) (J ×ˢ univ) (μ.prod ξ) := by
    rw [IntegrableOn, ← Measure.prod_restrict, Measure.restrict_univ]
    exact hθ.comp_snd (μ.restrict J)
  exact h.mono_set (fun z hz => ⟨⟨z, hz, rfl⟩, trivial⟩)

include hθ in
private theorem tensor_ofMeasure_localDensity {V : Set Y} (T : Distribution Y)
    (hT : ∀ f : SchwartzBruhat Y, support (f : Y → ℂ) ⊆ V → T f = ∫ y, θ y * f y ∂ξ)
    (f : SchwartzBruhat (X × Y)) (hf : support (f : X × Y → ℂ) ⊆ univ ×ˢ V) :
    Distribution.tensor (Distribution.ofMeasure μ) T f = ∫ z, θ z.2 * f z ∂(μ.prod ξ) := by
  have hI := (locallyIntegrable_comp_snd_prod μ ξ θ hθ).integrable_smul_right_of_hasCompactSupport
    f.continuous f.hasCompactSupport
  rw [Distribution.tensor_apply, Distribution.ofMeasure_apply,
    integral_prod (fun z => θ z.2 * f z) hI]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    rw [Distribution.partialApplySnd_apply, hT]
    · rfl
    · exact fun y hy => (hf (show (x, y) ∈ support (f : X × Y → ℂ) from hy)).2

end ProductDensity

section OpenEmbedding

variable {G H : Type*} [TopologicalSpace G] [TopologicalSpace H] [T2Space H]
  [MeasurableSpace G] [BorelSpace G] [MeasurableSpace H] [BorelSpace H]
  {j : G → H} (hj : IsOpenEmbedding j) (ν : Measure H)

private def extendTests : SchwartzBruhat G →ₗ[ℂ] SchwartzBruhat H :=
  (SchwartzBruhat.extendZero hj.isOpen_range).comp
    (Hecke.TestFunction.pullback hj.isEmbedding.toHomeomorph.symm).toLinearMap

private theorem isTestPushforward_extendTests :
    SchwartzBruhat.IsTestPushforward (ν.comap j) ν j (extendTests hj) := by
  intro f g
  let he := hj.measurableEmbedding
  calc
    _ = ∫ z in range j, extendAlongOpenEmbedding hj f z * g z ∂ν := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro z hz
      simp [extendAlongOpenEmbedding, hz]
    _ = _ := by
      rw [← he.map_comap, he.integral_map]
      simp only [extendAlongOpenEmbedding_apply]

end OpenEmbedding

section Slice

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
  [TotallyDisconnectedSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  {U C W : Set Y} (hU : IsOpen U) (hC : IsOpen C) (hW : IsOpen W) {y₀ : Y}
  (hyC : y₀ ∈ C) (hyW : y₀ ∈ W) (ν : Measure Y)
  (T₀ : Distribution Y) (T : Distribution U) (θ : Y → ℂ)
  (hθ : LocallyIntegrableOn θ W ν)
  (hTW : ∀ f : SchwartzBruhat Y, support (f : Y → ℂ) ⊆ W → T₀ f = ∫ y, θ y * f y ∂ν)
  (hTC : ∀ f : SchwartzBruhat U, support (f : U → ℂ) ⊆ Subtype.val ⁻¹' C →
    T₀ (SchwartzBruhat.extendZero hU f) = T f)

include hC hW hyC hyW hθ hTW hTC in
private theorem sliceLocalDensity (hyU : y₀ ∈ U) :
    ∃ V : Set U, IsOpen V ∧ (⟨y₀, hyU⟩ : U) ∈ V ∧
      ∃ ρ : U → ℂ, Integrable ρ (ν.comap Subtype.val) ∧
        ∀ f : SchwartzBruhat U, support (f : U → ℂ) ⊆ V →
          T f = ∫ z, ρ z * f z ∂(ν.comap Subtype.val) := by
  obtain ⟨K, hKc, hK, hyK, hKsub⟩ := exists_compact_clopen ((hC.inter hW).mem_nhds ⟨hyC, hyW⟩)
  let η := K.indicator θ
  have hη : Integrable η ν := (integrable_indicator_iff hK.2.measurableSet).2
    (hθ.integrableOn_compact_subset (hKsub.trans inter_subset_right) hKc)
  let ι : U → Y := Subtype.val
  let he := hU.isOpenEmbedding_subtypeVal.measurableEmbedding
  have hρη : Integrable (η ∘ ι) (ν.comap ι) := by
    apply he.integrable_map_iff.mp
    rw [he.map_comap]
    exact hη.mono_measure Measure.restrict_le_self
  refine ⟨ι ⁻¹' K, hK.2.preimage continuous_subtype_val, hyK, η ∘ ι, hρη, fun f hf => ?_⟩
  let g := SchwartzBruhat.extendZero hU f
  have hg (y : support (g : Y → ℂ)) : y.val ∈ K := by
    have hyU : y.val ∈ U := SchwartzBruhat.support_extendZero_subset hU f y.property
    exact hf (show f ⟨y.val, hyU⟩ ≠ 0 from fun h =>
      y.property ((SchwartzBruhat.extendZero_apply_of_mem hU f hyU).trans h))
  have hPg : support (g : Y → ℂ) ⊆ W := fun y hy => (hKsub (hg ⟨y, hy⟩)).2
  have hRC : support (f : U → ℂ) ⊆ Subtype.val ⁻¹' C := fun z hz => (hKsub (hf hz)).1
  rw [← hTC f hRC, hTW g hPg]
  calc
    _ = ∫ y, η y * g y ∂ν := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y => by
        by_cases hy : g y = 0
        · simp [hy]
        · change θ y * g y = K.indicator θ y * g y
          rw [indicator_of_mem (hg ⟨y, hy⟩)]
    _ = ∫ y in range ι, η y * g y ∂ν := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro y hy
      have hyU : y ∉ U := fun h => hy ⟨⟨y, h⟩, rfl⟩
      simp [g, SchwartzBruhat.extendZero_apply_of_not_mem hU f hyU]
    _ = _ := by
      rw [← he.map_comap, he.integral_map]
      simp only [g, ι, comp_apply, SchwartzBruhat.extendZero_apply_subtype]

end Slice

section Recovery

variable {F R H : Type*} [NontriviallyNormedField F] [ProperSpace F]
  [NormedRing R] [NormedAlgebra F R] [CompleteSpace R] [FiniteDimensional F R]
  [compactR : LocallyCompactSpace R] [disconnectedR : TotallyDisconnectedSpace R]
  [countableR : SecondCountableTopology R]
  [MeasurableSpace Rˣ] [BorelSpace Rˣ] [TopologicalSpace H] [T2Space H]
  [compactH : LocallyCompactSpace H] [disconnectedH : TotallyDisconnectedSpace H]
  [countableH : SecondCountableTopology H] [MeasurableSpace H] [borelH : BorelSpace H]

/-- A density at zero of the extended slice distribution yields a density at the center
of the original distribution. The ambient coordinate map embeds the units as a clopen chart. -/
def SemisimpleDensityRecoveryStatement [LocallyCompactSpace R] [TotallyDisconnectedSpace R]
    [SecondCountableTopology R] [LocallyCompactSpace H] [TotallyDisconnectedSpace H]
    [SecondCountableTopology H] [BorelSpace H] (α : R ≃ₐ[F] R) {j : Rˣ → H} (hj : IsOpenEmbedding j)
    (ν : Measure H) [IsFiniteMeasureOnCompacts ν] [ν.IsOpenPosMeasure] [(ν.comap j).IsHaarMeasure]
    [MeasurableSpace (adjointFixedAlgebra α)] [BorelSpace (adjointFixedAlgebra α)]
    (ρ : Measure (adjointFixedAlgebra α)) [ρ.IsAddHaarMeasure]
    (_hval : IsOpenEmbedding (Units.val : Rˣ → R)) (D : Distribution H) : Prop :=
  let S := adjointFixedAlgebra α
  let U := adjointConjugationDomain α
  let μ := ν.comap j
  let P₀ := extendTests hj
  IsClosed (range j) →
  ∀ (P : SchwartzBruhat (Rˣ × U) →ₗ[ℂ] SchwartzBruhat Rˣ)
    (T : Distribution U) (T₀ : Distribution S) (C W : Set S),
    SchwartzBruhat.IsTestPushforward (μ.prod (ρ.comap Subtype.val)) μ
      (adjointConjugationOnUnits α) P →
    ((D.comp P₀).comp P = Distribution.tensor (Distribution.ofMeasure μ) T) →
    IsOpen C → 0 ∈ C → C ⊆ U →
    (∀ f : SchwartzBruhat U, support (f : U → ℂ) ⊆ Subtype.val ⁻¹' C →
      T₀ (SchwartzBruhat.extendZero (isOpen_adjointConjugationDomain α) f) = T f) →
    IsOpen W → 0 ∈ W →
    (∃ θ : S → ℂ, LocallyIntegrableOn θ W ρ ∧ ∀ f : SchwartzBruhat S,
      support (f : S → ℂ) ⊆ W → T₀ f = ∫ y, θ y * f y ∂ρ) →
    ∃ V : Set H, IsOpen V ∧ j 1 ∈ V ∧ ∃ η : H → ℂ, Integrable η ν ∧
      ∀ f : SchwartzBruhat H, support (f : H → ℂ) ⊆ V → D f = ∫ x, η x * f x ∂ν

variable (α : R ≃ₐ[F] R) {j : Rˣ → H} (hj : IsOpenEmbedding j)
  (ν : Measure H) [IsFiniteMeasureOnCompacts ν] [ν.IsOpenPosMeasure] [(ν.comap j).IsHaarMeasure]

local notation "S" => adjointFixedAlgebra α
local notation "U" => adjointConjugationDomain α

variable [MeasurableSpace (adjointFixedAlgebra α)] [BorelSpace (adjointFixedAlgebra α)]
  (ρ : Measure (adjointFixedAlgebra α)) [ρ.IsAddHaarMeasure]

/-- Compose the two test pushforwards and transfer the tensor density through their
composition, evaluating the center at the identity conjugator and the zero slice point. -/
theorem semisimpleDensityRecovery (hval : IsOpenEmbedding (Units.val : Rˣ → R))
    (D : Distribution H) : SemisimpleDensityRecoveryStatement α hj ν ρ hval D := by
  rintro hjc P T T₀ C W hP hT hC hzero hCU hTC hW hzeroW ⟨θ, hθ, hTW⟩
  have hU := isOpen_adjointConjugationDomain α
  let : ProperSpace S := FiniteDimensional.proper F S
  let : SecondCountableTopology S := IsEmbedding.subtypeVal.secondCountableTopology
  let : SecondCountableTopology U := IsEmbedding.subtypeVal.secondCountableTopology
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let : LocallyCompactSpace Rˣ := hval.locallyCompactSpace
  let : T2Space Rˣ := hval.isEmbedding.t2Space
  let : SecondCountableTopology Rˣ := hval.isEmbedding.secondCountableTopology
  let : TotallyDisconnectedSpace Rˣ := hval.isEmbedding.isTotallyDisconnected_range.mp
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)
  let μ := ν.comap j
  let ξ := ρ.comap (Subtype.val : U → S)
  let : IsFiniteMeasureOnCompacts ξ := IsFiniteMeasureOnCompacts.comap' ρ continuous_subtype_val
    hU.isOpenEmbedding_subtypeVal.measurableEmbedding
  let : ξ.IsOpenPosMeasure := IsOpenPosMeasure.comap ρ hU.isOpenEmbedding_subtypeVal
  let y₀ : U := ⟨0, hCU hzero⟩
  obtain ⟨V, hV, hy₀V, θ', hθ', hT'⟩ := sliceLocalDensity hU hC hW hzero hzeroW ρ T₀ T θ
    hθ hTW hTC y₀.property
  let q := adjointConjugationOnUnits α
  have hq : Continuous q := hval.isEmbedding.continuous_iff.2 (by
    change Continuous (fun z : Rˣ × U => (q z).val)
    simp only [q, adjointConjugationOnUnits_val]
    rw [continuous_iff_continuousAt]
    intro z
    obtain ⟨d, hd, _⟩ := adjointConjugationMap_submersive α z.1 z.2.property
    let e : Rˣ × U → R × S := Prod.map Units.val Subtype.val
    have he : ContinuousAt e z := (hval.continuous.prodMap continuous_subtype_val).continuousAt
    change ContinuousAt (adjointConjugationMap α ∘ e) z
    exact hd.continuousAt.comp_of_eq he rfl)
  have hq₀ : q (1, y₀) = 1 := by
    apply Units.ext
    simp [q, y₀, adjointConjugationMap]
  let P' := (extendTests hj).comp P
  have hP' : SchwartzBruhat.IsTestPushforward (μ.prod ξ) ν (j ∘ q) P' := by
    intro f g
    change (∫ z, extendTests hj (P f) z * g z ∂ν) = ∫ x, f x * g (j (q x)) ∂(μ.prod ξ)
    rw [isTestPushforward_extendTests hj ν (P f) g]
    let g' : SchwartzBruhat Rˣ := ⟨g ∘ j, g.locallyConstant.comp_continuous hj.continuous,
      g.hasCompactSupport.comp_isClosedEmbedding ⟨hj.isEmbedding, hjc⟩⟩
    exact hP f g'
  obtain ⟨A, hA, hzA, η, hη, hident⟩ := pushforwardLocalDensity (P := P') D
    (univ ×ˢ V) (1, y₀) (hj.continuous.comp hq) hP' (isOpen_univ.prod hV) ⟨trivial, hy₀V⟩
    ⟨θ' ∘ Prod.snd, (locallyIntegrableOn_univ.2
        (locallyIntegrable_comp_snd_prod μ ξ θ' hθ')).mono_set (subset_univ _),
      fun f hf => by
        change ((D.comp (extendTests hj)).comp P) f = _
        rw [hT]
        exact tensor_ofMeasure_localDensity μ ξ θ' hθ' T hT' f hf⟩
  rw [Function.comp_apply, hq₀] at hzA
  exact ⟨A, hA, hzA, η, hη, hident⟩


end Recovery

end Langlands.BaseChange

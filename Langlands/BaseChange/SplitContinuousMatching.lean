import Langlands.BaseChange.CyclicProductConvolution
import Langlands.BaseChange.SplitMatchingOrbit
import Langlands.BaseChange.TwistedOrbitalConjugation

/-! # Concordant continuous compactly supported tests over a split algebra -/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory _root_.Topology
open Langlands.JacquetLanglands Langlands.QuotientIntegration Langlands.TraceFormula

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

universe u

section Pairs

variable {F : Type u} [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F]
  [T2Space F] {n m : ℕ}
  [LocallyCompactSpace (GeneralLinear n F)] [SecondCountableTopology (GeneralLinear n F)]
  [MeasurableSpace (GeneralLinear n F)] [BorelSpace (GeneralLinear n F)]
  [MeasurableSpace (GeneralLinear n (Fin (m + 1) → F))]
  [BorelSpace (GeneralLinear n (Fin (m + 1) → F))]

local notation "G" => GeneralLinear n F
local notation "GE" => GeneralLinear n (Fin (m + 1) → F)
local notation "κ" => splitGLCoordinates F n (m + 1)
local notation "σ" => splitCyclicShift F (m + 1)
local notation "θ" => MulEquiv.toMonoidHom (entrywiseAut σ n)
local notation "τ" => MonoidHom.id G

variable (μF : Measure (GeneralLinear n F)) [μF.IsHaarMeasure]

/-- Product Haar measure on the actual split-algebra matrix group. -/
def splitContinuousHaar : Measure GE := Measure.map (κ).symm (Measure.pi fun _ : Fin (m + 1) => μF)

omit [T2Space F] in
theorem splitContinuousHaar_isHaar : (splitContinuousHaar (m := m) μF).IsHaarMeasure :=
  (κ).symm.isHaarMeasure_map _

omit [IsTopologicalDivisionRing F] [T2Space F] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] [MeasurableSpace GE] [BorelSpace GE] in
private theorem continuous_splitTwist : Continuous (θ : GE → GE) := by
  have h : Continuous (σ : (Fin (m + 1) → F) → Fin (m + 1) → F) :=
    continuous_pi fun i => continuous_apply (finRotate (m + 1) i)
  exact Continuous.generalLinearGroup_map (f := (σ).toRingHom) h

omit [T2Space F] [LocallyCompactSpace G] [SecondCountableTopology G] in
private theorem coordinate_measure_from_associated
    (δ a : GE) (γ : G) (μδ : Measure (sigmaCentralizer σ n δ))
    (μγ : Measure (glCentralizer γ)) (h :
      Measure.map (fun c : sigmaCentralizer σ n δ => a⁻¹ * c.val * a) μδ =
        Measure.map (fun t : glCentralizer γ => baseChange F (Fin (m + 1) → F) n t.val) μγ) :
    Measure.map (fun c : sigmaCentralizer σ n δ => κ (a⁻¹ * c.val * a) 0) μδ =
      Measure.map Subtype.val μγ := by
  have hp : Measurable (fun x : GE => κ x 0) := ((continuous_apply 0).comp (κ).continuous).measurable
  have hbase : Continuous (baseChange F (Fin (m + 1) → F) n : G → GE) :=
    Continuous.generalLinearGroup_map (f := algebraMap F (Fin (m + 1) → F))
      (continuous_pi fun _ => continuous_id)
  have hb : Measurable (fun t : glCentralizer γ => baseChange F (Fin (m + 1) → F) n t.val) :=
    (hbase.comp continuous_subtype_val).measurable
  have hm := congrArg (Measure.map (fun x : GE => κ x 0)) h
  rw [Measure.map_map hp (by fun_prop), Measure.map_map hp hb] at hm
  simpa only [Function.comp_def, splitGLCoordinates_baseChange] using hm

set_option maxHeartbeats 900000 in
private theorem splitContinuousConcordAt
    (ψ : Fin (m + 1) → G → ℂ) (hc : ∀ i, Continuous (ψ i))
    (hs : ∀ i, HasCompactSupport (ψ i))
    (δ : GE) (γ : G) (hγ : IsRegularSemisimple γ) :
    ConcordAt σ (m + 1) μF (splitContinuousHaar μF)
      (fun x => ∏ i, ψ i (κ x i)) (splitFiberConvolution μF ψ) δ γ := by
  intro μδ _ _ μγ _ _ νδ νγ hνδ hνγ h
  obtain ⟨a, ha, hmeasure⟩ := h
  let δ' := twistedConj θ a δ
  have hN : cyclicNorm σ (m + 1) δ' = baseChange F (Fin (m + 1) → F) n γ := by
    change cyclicNorm σ (m + 1) (a⁻¹ * δ * entrywiseAut σ n a) = _
    rw [cyclicNorm_twistedConj, (isCyclicAlgebra_splitCyclicShift F m).pow_eq_one,
      entrywiseAut_one_apply, ha]
  have hγ' : (List.ofFn (κ δ')).prod = γ := by
    rw [← splitGLCoordinates_norm_zero, hN, splitGLCoordinates_baseChange]
  subst γ
  let y := (List.ofFn (κ δ')).prod
  let μE := splitContinuousHaar (m := m) μF
  let : μE.IsHaarMeasure := splitContinuousHaar_isHaar μF
  have hκ : MeasurePreserving κ μE (Measure.pi fun _ : Fin (m + 1) => μF) :=
    ⟨(κ).continuous.measurable, MeasurableEquiv.map_map_symm (κ).toHomeomorph.toMeasurableEquiv⟩
  let D := twistedCentralizer θ δ
  let D' := twistedCentralizer θ δ'
  let Z := glCentralizer y
  let eδ := twistedCentralizerConj θ δ a
  let μD : Measure D := μδ
  let : μD.IsHaarMeasure := inferInstanceAs μδ.IsHaarMeasure
  let : μD.IsMulRightInvariant := inferInstanceAs μδ.IsMulRightInvariant
  let μD' : Measure D' := Measure.map eδ μD
  let : μD'.IsHaarMeasure := eδ.isHaarMeasure_map μD
  let : μD'.IsMulRightInvariant := isMulRightInvariant_map eδ μD
  let νD' := Measure.map (twistedOrbitQuotientConj θ δ a) νδ
  have hνD' : IsCompatible D' μE μD' νD' :=
    isCompatible_map_twistedConj θ δ a μD μD' μE rfl νδ hνδ
  have hshift (x : GE) (i : Fin m) : κ (θ x) i.castSucc = κ x i.succ := by
    change κ (entrywiseAut σ n x) i.castSucc = _
    rw [splitGLCoordinates_shift, show finRotate (m + 1) i.castSucc = i.succ from finRotate_of_lt i.isLt]
  have hwrap (x : GE) : κ (θ x) (Fin.last m) = τ (κ x 0) := by
    change κ (entrywiseAut σ n x) (Fin.last m) = κ x 0
    rw [splitGLCoordinates_shift, finRotate_last]
  let e : D' ≃ₜ* Z := cyclicProductCentralizerEquiv κ θ τ hshift hwrap δ'
  have he : Measurable (e : D' → Z) := e.continuous.measurable
  have heδ : Measurable (eδ : D → D') := eδ.continuous.measurable
  have hZ : IsClosed (Z : Set G) :=
    isClosed_eq ((continuous_inv.mul continuous_const).mul continuous_id) continuous_const
  have hm : MeasurePreserving e μD' μγ := by
    refine ⟨he, (MeasurableEmbedding.subtype_coe hZ.measurableSet).map_injective ?_⟩
    change Measure.map Subtype.val (Measure.map e (Measure.map eδ μD)) = Measure.map Subtype.val μγ
    rw [Measure.map_map measurable_subtype_coe he,
      Measure.map_map (measurable_subtype_coe.comp he) heδ]
    have hcomp : (Subtype.val ∘ (e : D' → Z)) ∘ (eδ : D → D') =
        fun c : D => κ (a⁻¹ * c.val * a) 0 := by
      funext c
      change κ (↑(twistedCentralizerConj θ δ a c) : GE) 0 = _
      rw [twistedCentralizerConj_apply_coe]
    rw [hcomp]
    exact coordinate_measure_from_associated δ a y μδ μγ hmeasure
  let φ : GE → ℂ := fun x => ∏ i, ψ i (κ x i)
  have hcomp := cyclicProductConvolutionOrbitalIntegral_eq κ θ τ hshift hwrap δ'
    continuous_splitTwist continuous_id hκ hνD' hνγ hm
    (regularOrbitMap_isClosedEmbedding y hγ) ψ hc hs
  change twistedOrbitalIntegral θ δ νδ φ = _
  exact (twistedOrbitalIntegral_map_conj θ δ a νδ φ).2.symm.trans hcomp

end Pairs

/-- Split tensors with continuous compactly supported factors are concordant
with their ordered convolutions for the exact product Haar normalization. -/
def SplitContinuousMatchingStatement : Prop :=
  ∀ (F : Type u) [Field F] [TopologicalSpace F] [IsTopologicalDivisionRing F] [T2Space F]
    (n m : ℕ)
    [LocallyCompactSpace (GeneralLinear n F)] [SecondCountableTopology (GeneralLinear n F)]
    [MeasurableSpace (GeneralLinear n F)] [BorelSpace (GeneralLinear n F)]
    [MeasurableSpace (GeneralLinear n (Fin (m + 1) → F))]
    [BorelSpace (GeneralLinear n (Fin (m + 1) → F))]
    (μF : Measure (GeneralLinear n F)) [μF.IsHaarMeasure]
    (ψ : Fin (m + 1) → GeneralLinear n F → ℂ),
    (∀ i, Continuous (ψ i)) → (∀ i, HasCompactSupport (ψ i)) →
    let μE := splitContinuousHaar (m := m) μF
    let φ := fun x => ∏ i, ψ i (splitGLCoordinates F n (m + 1) x i)
    let f := splitFiberConvolution μF ψ
    μE.IsHaarMeasure ∧
    (Continuous φ ∧ HasCompactSupport φ) ∧
    (Continuous f ∧ HasCompactSupport f) ∧
    AreConcordant (splitCyclicShift F (m + 1)) (m + 1) μF μE φ f

theorem splitContinuousMatching : SplitContinuousMatchingStatement.{u} := by
  intro F _ _ _ _ n m _ _ _ _ _ _ μF _ ψ hc hs
  refine ⟨splitContinuousHaar_isHaar μF,
    splitTensorInCoordinates_continuous_hasCompactSupport (splitGLCoordinates F n (m + 1)) ψ hc hs,
    splitFiberConvolution_continuous_hasCompactSupport μF ψ hc hs, ?_, ?_⟩
  · intro γ _ hn
    exact (hn (isNorm_splitCyclicShift γ)).elim
  · intro δ γ _ hγ
    exact splitContinuousConcordAt μF ψ hc hs δ γ hγ

end Langlands.BaseChange

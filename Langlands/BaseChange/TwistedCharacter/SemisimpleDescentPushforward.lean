import Langlands.BaseChange.TwistedCharacter.SemisimpleConjugationSubmersion
import Langlands.HarmonicAnalysis.Distribution.OpenChartPushforward
import Langlands.HarmonicAnalysis.UnitConjugation.UnitHaarDensity

/-! # Test integration for semisimple conjugation -/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory MeasureTheory.Measure Function Set _root_.Topology HarmonicAnalysis
open scoped ENNReal NNReal

section Product

variable {X₁ X₂ Y₁ Y₂ : Type*} [MeasurableSpace X₁] [MeasurableSpace X₂]
  [MeasurableSpace Y₁] [MeasurableSpace Y₂]

private theorem comap_prodMap_of_measurableEmbedding {f : X₁ → Y₁} {g : X₂ → Y₂}
    (hf : MeasurableEmbedding f) (hg : MeasurableEmbedding g)
    (μ : Measure Y₁) (ν : Measure Y₂) [SFinite μ] [SFinite ν] [SFinite (ν.comap g)] :
    (μ.prod ν).comap (Prod.map f g) = (μ.comap f).prod (ν.comap g) := by
  have h := hf.prodMap hg
  apply h.map_injective
  rw [h.map_comap, ← map_prod_map _ _ hf.measurable hg.measurable,
    hf.map_comap, hg.map_comap, range_prodMap, prod_restrict]

end Product

variable {F R : Type*} [NontriviallyNormedField F] [ProperSpace F] [NormedRing R] [NormedAlgebra F R]
  [CompleteSpace R] [FiniteDimensional F R]
  (α : R ≃ₐ[F] R)

local notation "S" => adjointFixedAlgebra α
local notation "U" => adjointConjugationDomain α

/-- The normalized conjugation map with unit-group output. -/
def adjointConjugationOnUnits (z : Rˣ × U) : Rˣ :=
  z.1 * Units.map (adjointFixedAlgebra α).val.toMonoidHom z.2.property.1.unit * (Units.map α.toMonoidHom z.1)⁻¹

omit [CompleteSpace R] in
@[simp] theorem adjointConjugationOnUnits_val (z : Rˣ × U) :
    (adjointConjugationOnUnits α z).val = adjointConjugationMap α (z.1.val, z.2.val) := by
  rw [adjointConjugationOnUnits, Units.val_mul, Units.val_mul, Units.coe_map,
    IsUnit.unit_spec, adjointConjugationMap]
  change z.1.val * (1 + z.2.val.val) * ((Units.map α.toMonoidHom z.1)⁻¹ : Rˣ).val = _
  rw [show α z.1.val = (Units.map α.toMonoidHom z.1).val from rfl, Ring.inverse_unit]

variable [IsUltrametricDist R] [SecondCountableTopology R] [LocallyCompactSpace R]
  [TotallyDisconnectedSpace R] [MeasurableSpace R] [BorelSpace R]
  [MeasurableSpace Rˣ] [BorelSpace Rˣ]
  [MeasurableSpace (adjointFixedAlgebra α)] [BorelSpace (adjointFixedAlgebra α)]

/-- The conjugation submersion has a Schwartz–Bruhat test pushforward for actual
Haar measure on each of its unit-group factors and additive Haar on its slice. -/
def SemisimpleDescentPushforwardStatement (ν : Measure S) : Prop :=
  ∀ (μ : Measure Rˣ) [μ.IsHaarMeasure],
    ∃ P : SchwartzBruhat (Rˣ × U) →ₗ[ℂ] SchwartzBruhat Rˣ,
      SchwartzBruhat.IsTestPushforward (μ.prod (ν.comap Subtype.val)) μ
        (adjointConjugationOnUnits α) P

/-- Build the pushforward first with additive measures and then insert the unit
Haar weights. -/
theorem semisimpleDescentPushforward (ν : Measure S) [ν.IsAddHaarMeasure]
    (hval : IsOpenEmbedding (Units.val : Rˣ → R)) : SemisimpleDescentPushforwardStatement α ν := by
  intro μ _
  let ι : Rˣ × U → R × S := Prod.map Units.val Subtype.val
  have hU := isOpen_adjointConjugationDomain α
  have hi : IsOpenEmbedding ι := hval.prodMap hU.isOpenEmbedding_subtypeVal
  let e := hi.isEmbedding.toHomeomorph
  let a : Measure R := Measure.addHaar
  let r := a.comap (Units.val : Rˣ → R)
  let s := ν.comap (Subtype.val : U → S)
  have : LocallyCompactSpace Rˣ := hval.locallyCompactSpace
  have : T2Space Rˣ := hval.isEmbedding.t2Space
  have : SecondCountableTopology Rˣ := hval.isEmbedding.secondCountableTopology
  have : TotallyDisconnectedSpace Rˣ := hval.isEmbedding.isTotallyDisconnected_range.mp
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)
  let _ : ProperSpace S := FiniteDimensional.proper F S
  have : LocallyCompactSpace U := hU.locallyCompactSpace
  let _ : IsFiniteMeasureOnCompacts r :=
    IsFiniteMeasureOnCompacts.comap' a hval.continuous hval.measurableEmbedding
  let _ : IsFiniteMeasureOnCompacts s := IsFiniteMeasureOnCompacts.comap' ν
    continuous_subtype_val hU.isOpenEmbedding_subtypeVal.measurableEmbedding
  have : SecondCountableTopology S := IsEmbedding.subtypeVal.secondCountableTopology
  have : SecondCountableTopology U := IsEmbedding.subtypeVal.secondCountableTopology
  have : SFinite s := inferInstance
  have hprod : (a.prod ν).comap ι = r.prod s :=
    comap_prodMap_of_measurableEmbedding hval.measurableEmbedding
      hU.isOpenEmbedding_subtypeVal.measurableEmbedding a ν
  let f := adjointConjugationMap α
  have hd (z : R × S) (hz : z ∈ range ι) :
      ∃ d : R × S →L[F] R, HasStrictFDerivAt f d z ∧ Surjective d := by
    obtain ⟨⟨g, y⟩, rfl⟩ := hz
    exact adjointConjugationMap_submersive α g y.property
  have hfc : ContinuousOn f (range ι) := by
    intro z hz
    obtain ⟨d, hd, _⟩ := hd z hz
    exact hd.continuousAt.continuousWithinAt
  let _ : IsUltrametricDist S := IsUltrametricDist.subtype (fun x : R => x ∈ S)
  let _ : IsUltrametricDist (R × S) := ⟨fun a b c => by
    simpa only [Prod.dist_eq, max_assoc, max_comm, max_left_comm] using
      max_le_max (dist_triangle_max a.1 b.1 c.1) (dist_triangle_max a.2 b.2 c.2)⟩
  obtain ⟨P, hP⟩ := SchwartzBruhat.exists_testPushforward_of_additiveSubmersion
    (a.prod ν) a hi.isOpen_range f hfc hd
  let Q := P.comp (Hecke.TestFunction.pullback e.symm).toLinearMap
  have hQ : SchwartzBruhat.IsTestPushforward (r.prod s) a (f ∘ ι) Q := by
    intro φ ψ
    change (∫ y, P (Hecke.TestFunction.pullback e.symm φ) y * ψ y ∂a) = _
    rw [hP _ ψ]
    let j : range ι → R × S := Subtype.val
    have hjMap : (r.prod s).map e.toMeasurableEquiv = (a.prod ν).comap j := by
      rw [← hprod]
      change ((a.prod ν).comap (j ∘ e.toMeasurableEquiv)).map e.toMeasurableEquiv = _
      rw [← Measure.comap_comap (fun B hB => e.toMeasurableEquiv.measurableSet_image.mpr hB)
        Subtype.val_injective (fun B hB =>
          hi.isOpen_range.isOpenEmbedding_subtypeVal.measurableEmbedding.measurableSet_image.mpr hB),
        e.toMeasurableEquiv.measurableEmbedding.map_comap, e.toMeasurableEquiv.surjective.range_eq, restrict_univ]
    rw [← hjMap, e.toMeasurableEquiv.measurableEmbedding.integral_map]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      change φ (e.symm (e x)) * ψ (f (ι x)) = φ x * ψ (f (ι x))
      rw [e.symm_apply_apply]
  let q := adjointConjugationOnUnits α
  have hqval : (Units.val : Rˣ → R) ∘ q = f ∘ ι := funext (adjointConjugationOnUnits_val α)
  have hqc : Continuous q := hval.isEmbedding.continuous_iff.mpr (by
    rw [hqval]
    exact hfc.comp_continuous hi.continuous (fun x => mem_range_self x))
  rw [← hqval] at hQ
  obtain ⟨P', hP'⟩ := SchwartzBruhat.IsTestPushforward.exists_openTarget hval hqc hQ
  obtain ⟨w, hw, _, hHaar⟩ := UnitConjugation.unitHaarDensity hval a
  let η := r.withDensity (fun x => (w x : ℝ≥0∞))
  let _ : η.IsHaarMeasure := hHaar
  let c := Measure.haarScalarFactor μ η
  have hc : 0 < c := Measure.haarScalarFactor_pos_of_isHaarMeasure μ η
  let v := LocallyConstant.const Rˣ c * w
  have hv (x : Rˣ) : v x ≠ 0 := (mul_pos hc (hw x)).ne'
  have hμ : μ = r.withDensity (fun x => (v x : ℝ≥0∞)) := by
    rw [Measure.isMulLeftInvariant_eq_smul μ η, ← Measure.coe_nnreal_smul,
      ← withDensity_smul _ w.continuous.measurable.coe_nnreal_ennreal]
    congr 1
  let b : LocallyConstant (Rˣ × U) ℝ≥0 := v.comap ⟨Prod.fst, continuous_fst⟩
  obtain ⟨T, hT⟩ := SchwartzBruhat.IsTestPushforward.exists_weighted hP' b v hv
  change SchwartzBruhat.IsTestPushforward ((r.prod s).withDensity (fun z => (v z.1 : ℝ≥0∞)))
    (r.withDensity (fun y => (v y : ℝ≥0∞))) q T at hT
  rw [← prod_withDensity_left v.continuous.measurable.coe_nnreal_ennreal, ← hμ] at hT
  exact ⟨T, hT⟩

end Langlands.BaseChange

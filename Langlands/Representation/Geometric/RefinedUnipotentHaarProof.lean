import Langlands.Representation.Geometric.RefinedUnipotentHaarStatement
import Langlands.Group.GL.BlockModulusHaarProof
import Langlands.Representation.Smooth.SmallRealizationProof

/-! The actual Haar modulus of a refined product-Levi radical is the explicit
product of the block moduli. -/

open scoped NNReal ENNReal BigOperators
open MeasureTheory MeasureTheory.Measure

namespace Langlands.Geometric

universe uF

/-- Conjugation by an actual refined Levi element scales every Borel Haar measure
on the actual refinement radical by the inverse explicit modulus, and the actual
normalizer Haar character restricted to the refined Levi is the explicit modulus. -/
theorem padicRefinedUnipotentHaarModulus : PadicRefinedUnipotentHaarModulus.{uF} := by
  intro p hp F T n B S
  let := T.topology
  let := T.leviTopologicalGroup B
  let := T.refinedUnipotentLocallyCompactSpace B S
  let := T.valuativeRel
  let := T.localField
  have : ∀ k, SecondCountableTopology (GeneralLinear k F.Carrier) :=
    fun k => T.generalLinearSecondCountableTopology k
  have : SecondCountableTopology (B.Levi F.Carrier) := inferInstance
  have : SecondCountableTopology (refinedUnipotent F.Carrier B S) :=
    Topology.IsEmbedding.subtypeVal.secondCountableTopology
  have : ∀ i, SecondCountableTopology ((S i).parabolic F.Carrier) :=
    fun _ => Topology.IsEmbedding.subtypeVal.secondCountableTopology
  have : ∀ i, SecondCountableTopology ((S i).unipotentRadical F.Carrier) :=
    fun _ => Topology.IsEmbedding.subtypeVal.secondCountableTopology
  have : ∀ i, IsTopologicalGroup ((S i).unipotentRadical F.Carrier) :=
    fun i => T.unipotentRadicalTopologicalGroup (S i)
  have : ∀ i, LocallyCompactSpace ((S i).unipotentRadical F.Carrier) :=
    fun i => T.unipotentRadicalLocallyCompactSpace (S i)
  have hmeasure : ∀ (m : refinedLevi F.Carrier B S)
      [MeasurableSpace (refinedUnipotent F.Carrier B S)]
      [BorelSpace (refinedUnipotent F.Carrier B S)]
      (μ : Measure (refinedUnipotent F.Carrier B S)) [μ.IsHaarMeasure],
      μ.map (HaarModulus.normalizerConj (refinedUnipotent F.Carrier B S)
          (refinedLeviNormalizer F.Carrier B S m)) =
        ((T.refinedLeviModulus B S m : ℝ≥0)⁻¹) • μ := by
    intro m mU bU μ hμ
    obtain rfl := bU.measurable_eq
    let : MeasurableSpace (refinedUnipotent F.Carrier B S) := borel _
    have : BorelSpace (refinedUnipotent F.Carrier B S) := ⟨rfl⟩
    let : ∀ i, MeasurableSpace ((S i).unipotentRadical F.Carrier) := fun _ => borel _
    have : ∀ i, BorelSpace ((S i).unipotentRadical F.Carrier) := fun _ => ⟨rfl⟩
    have : BorelSpace (∀ i, (S i).unipotentRadical F.Carrier) := Pi.borelSpace
    let ν : (i : Fin B.length) → Measure ((S i).unipotentRadical F.Carrier) := fun _ => haar
    have : ∀ i, (ν i).IsHaarMeasure := fun _ => inferInstance
    have : ∀ i, SigmaFinite (ν i) := fun _ => inferInstance
    let mb : (i : Fin B.length) → (S i).Levi F.Carrier :=
      fun i => PadicField.TopologicalData.refinedLeviBlock B S i m
    let Φ : (∀ i, (S i).unipotentRadical F.Carrier) → ∀ i, (S i).unipotentRadical F.Carrier :=
      fun x i => (S i).leviAction F.Carrier (mb i) (x i)
    have hf (i : Fin B.length) : Measurable ((S i).leviAction F.Carrier (mb i)) :=
      (((S i).continuous_leviAction F.Carrier).comp
        (continuous_const.prodMk continuous_id)).measurable
    have hscale (i : Fin B.length) : (ν i).map ((S i).leviAction F.Carrier (mb i)) =
        ((T.leviModulus (S i) (mb i) : ℝ≥0)⁻¹) • ν i :=
      glBlockModulusHaar p F T (B.size i) (S i) (ν i) (mb i)
    have : ∀ i, SigmaFinite ((ν i).map ((S i).leviAction F.Carrier (mb i))) := fun i => by
      rw [hscale]
      infer_instance
    have hprod : (Measure.pi ν).map Φ =
        ((T.refinedLeviModulus B S m : ℝ≥0)⁻¹) • Measure.pi ν := by
      rw [Measure.pi_map_pi (fun i => (hf i).aemeasurable)]
      simp_rw [hscale]
      rw [HarmonicAnalysis.pi_nnreal_smul]
      congr 1
      rw [T.refinedLeviModulus_apply B S, Units.coe_prod]
      exact Finset.prod_inv_distrib _
    let e := refinedUnipotentRadicalEquiv B S F.Carrier
    let ρ : Measure (refinedUnipotent F.Carrier B S) := (Measure.pi ν).map e.symm
    have : ρ.IsHaarMeasure := e.symm.isHaarMeasure_map (Measure.pi ν)
    let a := HaarModulus.normalizerConj (refinedUnipotent F.Carrier B S)
      (refinedLeviNormalizer F.Carrier B S m)
    have ha : Measurable a := a.continuous.measurable
    have he : Measurable e.symm := e.symm.continuous.measurable
    have hΦ : Measurable Φ :=
      measurable_pi_iff.mpr fun i => (hf i).comp (measurable_pi_apply i)
    have hcoord : a ∘ e.symm = e.symm ∘ Φ := by
      funext x
      apply e.injective
      simp only [Function.comp_apply, ContinuousMulEquiv.apply_symm_apply]
      funext i
      have hb : (S i).leviEmbedding F.Carrier (mb i) = m.val i :=
        congrArg Subtype.val (((S i).leviEquiv F.Carrier).apply_symm_apply
          (refinedLeviEval F.Carrier B S i m))
      apply Subtype.ext
      apply Subtype.ext
      show m.val i * (x i).val.val * (m.val i)⁻¹ =
        (S i).leviEmbedding F.Carrier (mb i) * (x i).val.val *
          ((S i).leviEmbedding F.Carrier (mb i))⁻¹
      rw [hb]
    have hρ : ρ.map a = ((T.refinedLeviModulus B S m : ℝ≥0)⁻¹) • ρ := by
      change ((Measure.pi ν).map e.symm).map a = _
      rw [Measure.map_map ha he, hcoord, ← Measure.map_map he hΦ, hprod,
        Measure.map_smul _ he.aemeasurable]
    have hμρ := isMulLeftInvariant_eq_smul μ ρ
    rw [hμρ, Measure.map_smul _ ha.aemeasurable, hρ, smul_comm]
  refine ⟨hmeasure, ?_⟩
  apply MonoidHom.ext
  intro m
  apply Units.ext
  let : MeasurableSpace (refinedUnipotent F.Carrier B S) := borel _
  have : BorelSpace (refinedUnipotent F.Carrier B S) := ⟨rfl⟩
  obtain ⟨K₀⟩ : Nonempty (TopologicalSpace.PositiveCompacts (refinedUnipotent F.Carrier B S)) :=
    inferInstance
  let μ : Measure (refinedUnipotent F.Carrier B S) := haarMeasure K₀
  have h := HaarModulus.normalizerCharacter_smul_map (refinedUnipotent F.Carrier B S)
    (refinedLeviNormalizer F.Carrier B S m) μ
  rw [hmeasure m μ, smul_smul] at h
  have hK := congrArg (fun ν : Measure (refinedUnipotent F.Carrier B S) => ν (K₀ : Set _)) h
  simp only [Measure.smul_apply, μ, haarMeasure_self, ENNReal.smul_def, smul_eq_mul,
    mul_one] at hK
  have h1 : (HaarModulus.normalizerCharacter (refinedUnipotent F.Carrier B S)
      (refinedLeviNormalizer F.Carrier B S m) : ℝ≥0) *
        (T.refinedLeviModulus B S m : ℝ≥0)⁻¹ = 1 := by
    exact_mod_cast hK
  exact (mul_inv_eq_one₀ (T.refinedLeviModulus B S m).ne_zero).mp h1

end Langlands.Geometric

import Langlands.Representation.Geometric.CorrectionSubgroupDiagonalHaarProof
import Langlands.AllField.Representation.Geometric.CorrectionSubgroupDiagonalHaarStatement
import Langlands.AllField.Representation.Geometric.StandardIntersectionsProof
/-! Actual coordinate Haar measure and diagonal modulus for full correction subgroups. -/

open MeasureTheory MeasureTheory.Measure
open scoped BigOperators NNReal ENNReal

namespace Langlands.AllField.Geometric
open Langlands.Geometric hiding CorrectionSubgroupDiagonalHaarStatement PadicStandardIntersectionsTheorem correctionSubgroupDiagonalHaar padicStandardIntersectionsTheorem
open Langlands.AllField.Geometric

universe u

variable {n : ℕ} (B C : GeneralLinear.BlockShape n) (w : Equiv.Perm (Fin n))
  (R : Type u) [CommRing R]

section Measure


end Measure

universe uF

/-- The residue-normalized root product is the actual diagonal Haar modulus. -/
theorem correctionSubgroupDiagonalHaar :
    CorrectionSubgroupDiagonalHaarStatement.{uF} := by
  intro F _ T n B C w
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearLocallyCompactSpace n
  let := T.secondCountableTopology
  let := T.pseudoMetrizableSpace
  dsimp only
  intro t d hd
  let H := correctionSubgroup B C w F
  let hH : IsClosed (H : Set (GeneralLinear n F)) :=
    General.isClosed_correctionSubgroup
      (B.unipotentSubgroup F) (C.parabolic F)
      (GeneralLinear.permutation n F w)
      (B.isClosed_unipotentSubgroup F) (C.isClosed_parabolic F)
  let : LocallyCompactSpace H := hH.locallyCompactSpace
  let : MeasurableSpace F := borel _
  let : BorelSpace F := ⟨rfl⟩
  let : MeasurableSpace H := borel _
  let : BorelSpace H := ⟨rfl⟩
  let e := correctionCoordinatesHomeomorph B C w F
  let : SecondCountableTopology H := e.secondCountableTopology
  let : TopologicalSpace.PseudoMetrizableSpace H := e.isInducing.pseudoMetrizableSpace
  let ν : CorrectionEntry B C w → Measure F := fun _ => addHaar
  let : ∀ ab, (ν ab).IsAddHaarMeasure := fun _ => inferInstance
  let : ∀ ab, SigmaFinite (ν ab) := fun _ => inferInstance
  let a : CorrectionEntry B C w → Fˣ :=
    fun ab => t ab.1.1 / t ab.1.2
  let c : ℝ≥0ˣ := ∏ ab, T.normalizedAbsUnits (a ab)
  let f : CorrectionEntry B C w → F → F :=
    fun ab x => (a ab : F) * x
  have hf (ab : CorrectionEntry B C w) : Measurable (f ab) :=
    (continuous_const.mul continuous_id).measurable
  have hscale (ab : CorrectionEntry B C w) :
      (ν ab).map (f ab) = (T.normalizedAbsUnits (a ab) : ℝ≥0)⁻¹ • ν ab :=
    Langlands.AllField.HarmonicAnalysis.padicScalarHaarScaling F T (ν ab) (a ab)
  let : ∀ ab, SigmaFinite ((ν ab).map (f ab)) := fun ab => by
    rw [hscale ab]
    infer_instance
  have hprod :
      (Measure.pi ν).map (fun X ab => f ab (X ab)) = (c : ℝ≥0)⁻¹ • Measure.pi ν := by
    rw [Measure.pi_map_pi (fun ab => (hf ab).aemeasurable)]
    simp_rw [hscale]
    rw [HarmonicAnalysis.pi_nnreal_smul]
    simp only [c, Units.coe_prod, Finset.prod_inv_distrib]
  let ρ : Measure H := (Measure.pi ν).map e.symm
  let : ρ.IsHaarMeasure := correctionCoordinateHaar B C w F ν
  let : ρ.Regular := inferInstance
  let α := HaarModulus.normalizerConj H d
  have hcoord : α ∘ e.symm = e.symm ∘ (fun X ab => f ab (X ab)) := by
    funext X
    apply e.injective
    simp only [Function.comp_apply, Homeomorph.apply_symm_apply]
    funext ab
    change correctionCoordinates B C w F (α (e.symm X)) ab = f ab (X ab)
    rw [correctionCoordinates_diagonal_conj B C w F t d hd]
    exact congrArg ((a ab : F) * ·) (congrFun (e.apply_symm_apply X) ab)
  have hF : Measurable (fun (X : CorrectionEntry B C w → F) ab => f ab (X ab)) :=
    measurable_pi_iff.mpr (fun ab => (hf ab).comp (measurable_pi_apply ab))
  have hα : Measurable (α : H → H) := α.continuous.measurable
  have hρ : ρ.map α = (c : ℝ≥0)⁻¹ • ρ := by
    change ((Measure.pi ν).map e.symm).map α = _
    rw [Measure.map_map hα e.symm.measurable, hcoord,
      ← Measure.map_map e.symm.measurable hF, hprod,
      Measure.map_smul _ e.symm.measurable.aemeasurable]
  have hchar := HaarModulus.normalizerCharacter_smul_map H d ρ
  rw [hρ, smul_smul] at hchar
  have hfactor : (HaarModulus.normalizerCharacter H d : ℝ≥0) * (c : ℝ≥0)⁻¹ = 1 := by
    calc
      _ = haarScalarFactor
          (((HaarModulus.normalizerCharacter H d : ℝ≥0) * (c : ℝ≥0)⁻¹) • ρ) ρ := by
        simp only [haarScalarFactor_smul, haarScalarFactor_self, smul_eq_mul, mul_one]
      _ = 1 := by simp only [hchar, haarScalarFactor_self]
  have hval : (HaarModulus.normalizerCharacter H d : ℝ≥0) = (c : ℝ≥0) := by
    calc
      (HaarModulus.normalizerCharacter H d : ℝ≥0) =
          ((HaarModulus.normalizerCharacter H d : ℝ≥0) * (c : ℝ≥0)⁻¹) * c := by
        rw [mul_assoc, inv_mul_cancel₀ c.ne_zero, mul_one]
      _ = c := by rw [hfactor, one_mul]
  have hunit : HaarModulus.closedNormalizerCharacter H hH d = c := by
    rw [HaarModulus.closedNormalizerCharacter_eq]
    exact Units.ext hval
  change HaarModulus.closedNormalizerCharacter H hH d = _
  refine hunit.trans ?_
  dsimp only [c, a, CorrectionEntry, CorrectionAllowed]
  congr 1
  funext ab
  exact map_div T.normalizedAbsUnits _ _

end Langlands.AllField.Geometric

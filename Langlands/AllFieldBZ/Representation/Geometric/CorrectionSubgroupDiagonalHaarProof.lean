import Langlands.AllFieldBZ.HarmonicAnalysis.PadicScalarHaarScalingProof
import Langlands.AllFieldBZ.Representation.Geometric.CorrectionSubgroupCoordinates
import Langlands.AllFieldBZ.Representation.Geometric.CorrectionSubgroupDiagonalHaarStatement
import Langlands.Representation.Geometric.CorrectionSubgroupDiagonalHaarProof

/-!
# All-field port of `Langlands.Representation.Geometric.CorrectionSubgroupDiagonalHaarProof`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Geometric.CorrectionSubgroupDiagonalHaarProof` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
open MeasureTheory
open MeasureTheory.Measure
open scoped BigOperators
open scoped NNReal
open scoped ENNReal
namespace Langlands.AllFieldBZ.Geometric
open Langlands.Geometric hiding CorrectionSubgroupDiagonalHaarStatement PadicParabolicBruhatTheorem PadicStandardIntersectionsTheorem correctionSubgroupDiagonalHaar padicStandardIntersectionsTheorem
universe u

variable {n : ℕ} (B C : GeneralLinear.BlockShape n) (w : Equiv.Perm (Fin n))
  (R : Type u) [CommRing R]

private theorem _root_.Langlands.Geometric.correctionTranslation_depends (a : correctionSubgroup B C w R)
    (ab : CorrectionEntry B C w) (X Y : CorrectionEntry B C w → R)
    (h : ∀ cd, correctionGap B C w cd < correctionGap B C w ab → X cd = Y cd) :
    (correctionCoordinates B C w R
        (a * (correctionCoordinates B C w R).symm X) - X) ab =
      (correctionCoordinates B C w R
        (a * (correctionCoordinates B C w R).symm Y) - Y) ab := by
  simp only [Pi.sub_apply, correctionCoordinates_mul_allowed, Equiv.apply_symm_apply]
  have hs :
      (∑ k : CorrectionIntermediate B C w ab,
        correctionCoordinates B C w R a ⟨(ab.1.1, k.val), k.2.1⟩ *
          X ⟨(k.val, ab.1.2), k.2.2⟩) =
      (∑ k : CorrectionIntermediate B C w ab,
        correctionCoordinates B C w R a ⟨(ab.1.1, k.val), k.2.1⟩ *
          Y ⟨(k.val, ab.1.2), k.2.2⟩) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [h _ (correctionIntermediate_gap B C w ab k).2]
  rw [hs]
  abel

section Measure
variable [TopologicalSpace R] [IsTopologicalRing R] [SecondCountableTopology R]
  [MeasurableSpace R] [BorelSpace R]
  [MeasurableSpace (correctionSubgroup B C w R)]
  [BorelSpace (correctionSubgroup B C w R)]

end Measure
universe uF

/-- The residue-normalized root product is the actual diagonal Haar modulus. -/
theorem correctionSubgroupDiagonalHaar :
    CorrectionSubgroupDiagonalHaarStatement.{uF} := by
  intro F T n B C w
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearLocallyCompactSpace n
  let := T.secondCountableTopology
  let := T.pseudoMetrizableSpace
  dsimp only
  intro t d hd
  let H := correctionSubgroup B C w F.Carrier
  let hH : IsClosed (H : Set (GeneralLinear n F.Carrier)) :=
    General.isClosed_correctionSubgroup
      (B.unipotentSubgroup F.Carrier) (C.parabolic F.Carrier)
      (GeneralLinear.permutation n F.Carrier w)
      (B.isClosed_unipotentSubgroup F.Carrier) (C.isClosed_parabolic F.Carrier)
  let : LocallyCompactSpace H := hH.locallyCompactSpace
  let : MeasurableSpace F.Carrier := borel _
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let : MeasurableSpace H := borel _
  let : BorelSpace H := ⟨rfl⟩
  let e := correctionCoordinatesHomeomorph B C w F.Carrier
  let : SecondCountableTopology H := e.secondCountableTopology
  let : TopologicalSpace.PseudoMetrizableSpace H := e.isInducing.pseudoMetrizableSpace
  let ν : CorrectionEntry B C w → Measure F.Carrier := fun _ => addHaar
  let : ∀ ab, (ν ab).IsAddHaarMeasure := fun _ => inferInstance
  let : ∀ ab, SigmaFinite (ν ab) := fun _ => inferInstance
  let a : CorrectionEntry B C w → F.Carrierˣ :=
    fun ab => t ab.1.1 / t ab.1.2
  let c : ℝ≥0ˣ := ∏ ab, T.normalizedAbsUnits (a ab)
  let f : CorrectionEntry B C w → F.Carrier → F.Carrier :=
    fun ab x => (a ab : F.Carrier) * x
  have hf (ab : CorrectionEntry B C w) : Measurable (f ab) :=
    (continuous_const.mul continuous_id).measurable
  have hscale (ab : CorrectionEntry B C w) :
      (ν ab).map (f ab) = (T.normalizedAbsUnits (a ab) : ℝ≥0)⁻¹ • ν ab :=
    HarmonicAnalysis.padicScalarHaarScaling F T (ν ab) (a ab)
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
  let : ρ.IsHaarMeasure := correctionCoordinateHaar B C w F.Carrier ν
  let : ρ.Regular := inferInstance
  let α := HaarModulus.normalizerConj H d
  have hcoord : α ∘ e.symm = e.symm ∘ (fun X ab => f ab (X ab)) := by
    funext X
    apply e.injective
    simp only [Function.comp_apply, Homeomorph.apply_symm_apply]
    funext ab
    change correctionCoordinates B C w F.Carrier (α (e.symm X)) ab = f ab (X ab)
    rw [correctionCoordinates_diagonal_conj B C w F.Carrier t d hd]
    exact congrArg ((a ab : F.Carrier) * ·) (congrFun (e.apply_symm_apply X) ab)
  have hF : Measurable (fun (X : CorrectionEntry B C w → F.Carrier) ab => f ab (X ab)) :=
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

end Langlands.AllFieldBZ.Geometric

import Langlands.Group.GL.BlockModulusHaarStatement
import Langlands.Group.GL.BlockUnipotentHaarProof
import Langlands.HarmonicAnalysis.PadicRectangularHaarScalingProof
import Mathlib.MeasureTheory.Measure.Haar.Unique

open MeasureTheory MeasureTheory.Measure
open scoped BigOperators NNReal ENNReal

namespace Langlands

private theorem pi_nnreal_smul {ι : Type*} [Fintype ι] {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] (μ : (i : ι) → Measure (X i))
    [∀ i, SigmaFinite (μ i)] (c : ι → ℝ≥0) :
    Measure.pi (fun i => c i • μ i) = (∏ i, c i) • Measure.pi μ := by
  apply Measure.pi_eq
  intro s _
  simp only [Measure.smul_apply, Measure.pi_pi]
  exact (Finset.prod_smul _ _ _).symm

namespace PadicField.TopologicalData

universe uF
variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
  {n : ℕ} (B : GeneralLinear.BlockShape n)

theorem leviModulus_eq_upperPair_prod (m : B.Levi F.Carrier) :
    (T.leviModulus B m : ℝ≥0) = ∏ ij : B.UpperPair,
      (T.determinantNorm (B.size ij.1.1) (m ij.1.1) : ℝ≥0) ^ B.size ij.1.2 /
        (T.determinantNorm (B.size ij.1.2) (m ij.1.2) : ℝ≥0) ^ B.size ij.1.1 := by
  classical
  rw [T.leviModulus_apply]
  simp only [Units.coe_prod, Units.val_div_eq_div_val, Units.val_pow_eq_pow_val]
  let f : Fin B.length × Fin B.length → ℝ≥0 := fun ij =>
    (T.determinantNorm (B.size ij.1) (m ij.1) : ℝ≥0) ^ B.size ij.2 /
      (T.determinantNorm (B.size ij.2) (m ij.2) : ℝ≥0) ^ B.size ij.1
  change (∏ i, ∏ j ∈ Finset.univ.filter (fun j => i < j), f (i,j)) =
    ∏ ij : {ij : Fin B.length × Fin B.length // ij.1 < ij.2}, f ij
  rw [← Finset.prod_subtype (Finset.univ.filter (fun ij : Fin B.length × Fin B.length =>
    ij.1 < ij.2)) (by simp) f]
  simp only [Finset.prod_filter, ← Finset.univ_product_univ, Finset.prod_product]

end PadicField.TopologicalData

universe uF

theorem glBlockModulusHaarStatement_of_prerequisites
    (hrect : HarmonicAnalysis.PadicRectangularHaarScalingStatement.{uF})
    (hhaar : GLBlockUnipotentCoordinateHaarStatement.{uF}) :
    GLBlockModulusHaarStatement.{uF} := by
  intro p hp F T n B
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.secondCountableTopology
  let := T.unipotentRadicalTopologicalGroup B
  let := T.unipotentRadicalT2Space B
  let := T.unipotentRadicalLocallyCompactSpace B
  intro mU bU
  obtain rfl := bU.measurable_eq
  let : MeasurableSpace (B.unipotentRadical F.Carrier) := borel _
  let : BorelSpace (B.unipotentRadical F.Carrier) := ⟨rfl⟩
  intro μ hμ m
  let Block := fun ij : B.UpperPair =>
    Matrix (Fin (B.size ij.1.1)) (Fin (B.size ij.1.2)) F.Carrier
  let : ∀ ij, MeasurableSpace (Block ij) := fun _ => borel _
  let : ∀ ij, BorelSpace (Block ij) := fun _ => ⟨rfl⟩
  let : ∀ ij, SecondCountableTopology (Block ij) := fun ij =>
    inferInstanceAs (SecondCountableTopology
      (Fin (B.size ij.1.1) → Fin (B.size ij.1.2) → F.Carrier))
  let : ∀ ij, LocallyCompactSpace (Block ij) := fun ij =>
    inferInstanceAs (LocallyCompactSpace
      (Fin (B.size ij.1.1) → Fin (B.size ij.1.2) → F.Carrier))
  let : ∀ ij, OpensMeasurableSpace (Block ij) := fun _ => inferInstance
  let : BorelSpace (B.RadicalCoordinates F.Carrier) := Pi.borelSpace
  let : SecondCountableTopology (B.unipotentRadical F.Carrier) :=
    (B.radicalCoordinatesHomeomorph F.Carrier).secondCountableTopology
  let ν : (ij : B.UpperPair) → Measure (Block ij) := fun _ => addHaar
  let : ∀ ij, (ν ij).IsAddHaarMeasure := fun _ => inferInstance
  let : ∀ ij, SigmaFinite (ν ij) := fun _ => inferInstance
  let c : B.UpperPair → ℝ≥0 := fun ij =>
    ((T.determinantNorm (B.size ij.1.1) (m ij.1.1) : ℝ≥0) ^ B.size ij.1.2 /
      (T.determinantNorm (B.size ij.1.2) (m ij.1.2) : ℝ≥0) ^ B.size ij.1.1)⁻¹
  let f : (ij : B.UpperPair) → Block ij → Block ij := fun ij X =>
    (m ij.1.1).val * X * ((m ij.1.2)⁻¹).val
  have hf (ij : B.UpperPair) : Measurable (f ij) := by
    exact ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).measurable
  have hscale (ij : B.UpperPair) : (ν ij).map (f ij) = c ij • ν ij :=
    hrect p F T (B.size ij.1.1) (B.size ij.1.2) (ν ij) (m ij.1.1) (m ij.1.2)
  let : ∀ ij, SigmaFinite ((ν ij).map (f ij)) := fun ij => by
    rw [hscale]
    infer_instance
  have hprod : (Measure.pi ν).map (fun X ij => f ij (X ij)) =
      ((T.leviModulus B m : ℝ≥0)⁻¹) • Measure.pi ν := by
    rw [Measure.pi_map_pi (fun ij => (hf ij).aemeasurable)]
    simp_rw [hscale]
    rw [pi_nnreal_smul]
    congr 1
    rw [T.leviModulus_eq_upperPair_prod B]
    exact Finset.prod_inv_distrib _
  let e := B.radicalCoordinatesHomeomorph F.Carrier
  let ρ := (Measure.pi ν).map e.symm
  have : ρ.IsHaarMeasure := hhaar p F T n B ν
  have ha : Measurable (B.leviAction F.Carrier m) :=
    ((B.continuous_leviAction F.Carrier).comp (continuous_const.prodMk continuous_id)).measurable
  have hcoord : (B.leviAction F.Carrier m) ∘ e.symm =
      e.symm ∘ (fun X ij => f ij (X ij)) := by
    funext X
    apply e.injective
    simp only [Function.comp_apply, Homeomorph.apply_symm_apply]
    funext ij
    exact B.radicalCoordinates_leviAction_symm F.Carrier m X ij
  have hF : Measurable (fun (X : B.RadicalCoordinates F.Carrier) ij => f ij (X ij)) :=
    measurable_pi_iff.mpr (fun ij => (hf ij).comp (measurable_pi_apply ij))
  have hρ : ρ.map (B.leviAction F.Carrier m) =
      ((T.leviModulus B m : ℝ≥0)⁻¹) • ρ := by
    change ((Measure.pi ν).map e.symm).map _ = _
    rw [Measure.map_map ha e.symm.measurable, hcoord,
      ← Measure.map_map e.symm.measurable hF, hprod,
      Measure.map_smul _ e.symm.measurable.aemeasurable]
  have hμρ := isMulLeftInvariant_eq_smul μ ρ
  rw [hμρ, Measure.map_smul _ ha.aemeasurable, hρ, smul_comm]

/-- The coordinate-Haar result reduces the modulus formula to rectangular scaling. -/
theorem glBlockModulusHaarStatement_of_rectangular
    (hrect : HarmonicAnalysis.PadicRectangularHaarScalingStatement.{uF}) :
    GLBlockModulusHaarStatement.{uF} :=
  glBlockModulusHaarStatement_of_prerequisites hrect glBlockUnipotentCoordinateHaarStatement

/-- The explicit block modulus is the Haar module of Levi conjugation. -/
theorem glBlockModulusHaar : GLBlockModulusHaarStatement.{uF} :=
  glBlockModulusHaarStatement_of_rectangular
    HarmonicAnalysis.padicRectangularHaarScalingStatement

end Langlands

import Langlands.Group.GL.BlockUnipotentHaarStatement
import Langlands.HarmonicAnalysis.TriangularTranslationProof
import Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof

open MeasureTheory MeasureTheory.Measure
open scoped BigOperators

namespace Langlands.GeneralLinear.BlockShape

universe u

variable {n : ℕ} (B : BlockShape n) (R : Type u) [CommRing R]

private theorem coordinateCorrection_depends (a : B.unipotentRadical R)
    (ij : B.UpperPair) (X Y : B.RadicalCoordinates R)
    (h : ∀ kl : B.UpperPair,
      kl.1.2.val - kl.1.1.val < ij.1.2.val - ij.1.1.val → X kl = Y kl) :
    (B.radicalCoordinates R (a * (B.radicalCoordinates R).symm X) - X) ij =
      (B.radicalCoordinates R (a * (B.radicalCoordinates R).symm Y) - Y) ij := by
  simp only [Pi.sub_apply, B.radicalCoordinates_mul R, Equiv.apply_symm_apply]
  have hs :
      (∑ k : {k : Fin B.length // ij.1.1 < k ∧ k < ij.1.2},
        B.radicalCoordinates R a ⟨(ij.1.1, k), k.2.1⟩ * X ⟨(k, ij.1.2), k.2.2⟩) =
      (∑ k : {k : Fin B.length // ij.1.1 < k ∧ k < ij.1.2},
        B.radicalCoordinates R a ⟨(ij.1.1, k), k.2.1⟩ * Y ⟨(k, ij.1.2), k.2.2⟩ :
          Matrix (Fin (B.size ij.1.1)) (Fin (B.size ij.1.2)) R) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [h ⟨(k, ij.1.2), k.2.2⟩]
    have hi : ij.1.1.val < k.val.val := k.2.1
    have hj : k.val.val < ij.1.2.val := k.2.2
    dsimp
    omega
  rw [hs]
  abel

section Measure

variable [TopologicalSpace R] [IsTopologicalRing R] [SecondCountableTopology R]
  [mBlock : ∀ ij : B.UpperPair,
    MeasurableSpace (Matrix (Fin (B.size ij.1.1)) (Fin (B.size ij.1.2)) R)]
  [bBlock : ∀ ij : B.UpperPair,
    BorelSpace (Matrix (Fin (B.size ij.1.1)) (Fin (B.size ij.1.2)) R)]
  [MeasurableSpace (B.unipotentRadical R)] [BorelSpace (B.unipotentRadical R)]

include bBlock

omit [MeasurableSpace (B.unipotentRadical R)] [BorelSpace (B.unipotentRadical R)] in
theorem coordinateLeftTranslation_preserving_of_triangular
    (htri : Langlands.HarmonicAnalysis.FiniteTriangularTranslationStatement.{0,u})
    (μ : (ij : B.UpperPair) →
      Measure (Matrix (Fin (B.size ij.1.1)) (Fin (B.size ij.1.2)) R))
    [∀ ij, SigmaFinite (μ ij)] [∀ ij, (μ ij).IsAddLeftInvariant]
    (a : B.unipotentRadical R) :
    MeasurePreserving
      (fun X => B.radicalCoordinates R (a * (B.radicalCoordinates R).symm X))
      (Measure.pi μ) (Measure.pi μ) := by
  let : ∀ ij : B.UpperPair,
      SecondCountableTopology (Matrix (Fin (B.size ij.1.1)) (Fin (B.size ij.1.2)) R) :=
    fun ij => inferInstanceAs
      (SecondCountableTopology (Fin (B.size ij.1.1) → Fin (B.size ij.1.2) → R))
  let : ∀ ij : B.UpperPair,
      OpensMeasurableSpace (Matrix (Fin (B.size ij.1.1)) (Fin (B.size ij.1.2)) R) :=
    fun ij => by
      let := bBlock ij
      infer_instance
  let : ∀ ij : B.UpperPair,
      MeasurableAdd₂ (Matrix (Fin (B.size ij.1.1)) (Fin (B.size ij.1.2)) R) :=
    fun ij => by
      let := bBlock ij
      infer_instance
  let f : B.RadicalCoordinates R → B.RadicalCoordinates R :=
    fun X => B.radicalCoordinates R (a * (B.radicalCoordinates R).symm X) - X
  have hf : Continuous f := by
    exact ((B.continuous_radicalCoordinates R).comp
      (continuous_const.mul (B.continuous_radicalCoordinates_symm R))).sub continuous_id
  have hp := htri B.UpperPair
    (fun ij => Matrix (Fin (B.size ij.1.1)) (Fin (B.size ij.1.2)) R)
    μ (fun ij => ij.1.2.val - ij.1.1.val) f hf.measurable
    (B.coordinateCorrection_depends R a)
  have he : (fun X ij => f X ij + X ij) =
      (fun X => B.radicalCoordinates R (a * (B.radicalCoordinates R).symm X)) := by
    funext X ij
    exact sub_add_cancel _ _
  rw [he] at hp
  exact hp

theorem coordinateHaar_of_triangular
    (htri : Langlands.HarmonicAnalysis.FiniteTriangularTranslationStatement.{0,u})
    (μ : (ij : B.UpperPair) →
      Measure (Matrix (Fin (B.size ij.1.1)) (Fin (B.size ij.1.2)) R))
    [∀ ij, SigmaFinite (μ ij)] [∀ ij, (μ ij).IsAddHaarMeasure] :
    ((Measure.pi μ).map (B.radicalCoordinates R).symm).IsHaarMeasure := by
  let : ∀ ij : B.UpperPair,
      SecondCountableTopology (Matrix (Fin (B.size ij.1.1)) (Fin (B.size ij.1.2)) R) :=
    fun ij => inferInstanceAs
      (SecondCountableTopology (Fin (B.size ij.1.1) → Fin (B.size ij.1.2) → R))
  let : ∀ ij : B.UpperPair,
      OpensMeasurableSpace (Matrix (Fin (B.size ij.1.1)) (Fin (B.size ij.1.2)) R) :=
    fun ij => by
      let := bBlock ij
      infer_instance
  let : BorelSpace (B.RadicalCoordinates R) := Pi.borelSpace
  let e := B.radicalCoordinatesHomeomorph R
  have he : Measurable (B.radicalCoordinates R).symm := e.symm.measurable
  have : IsFiniteMeasureOnCompacts
      ((Measure.pi μ).map (B.radicalCoordinates R).symm) :=
    IsFiniteMeasureOnCompacts.map (Measure.pi μ) e.symm
  have : IsOpenPosMeasure ((Measure.pi μ).map (B.radicalCoordinates R).symm) :=
    e.symm.continuous.isOpenPosMeasure_map e.symm.surjective
  refine { map_mul_left_eq_self := fun a => ?_ }
  have hp := B.coordinateLeftTranslation_preserving_of_triangular R htri μ a
  have hm : Measurable (fun x : B.unipotentRadical R => a * x) :=
    (continuous_const.mul continuous_id).measurable
  rw [Measure.map_map hm he]
  have heq :
      (fun x : B.unipotentRadical R => a * x) ∘ (B.radicalCoordinates R).symm =
      (B.radicalCoordinates R).symm ∘
        (fun X => B.radicalCoordinates R (a * (B.radicalCoordinates R).symm X)) := by
    funext X
    simp
  rw [heq, ← Measure.map_map he hp.measurable, hp.map_eq]

end Measure

end Langlands.GeneralLinear.BlockShape

namespace Langlands

universe uF

theorem glBlockUnipotentCoordinateHaarStatement_of_triangular
    (htri : HarmonicAnalysis.FiniteTriangularTranslationStatement.{0,uF}) :
    GLBlockUnipotentCoordinateHaarStatement.{uF} := by
  intro p hp F T n B
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.secondCountableTopology
  let : ∀ ij : B.UpperPair,
      MeasurableSpace (Matrix (Fin (B.size ij.1.1)) (Fin (B.size ij.1.2)) F.Carrier) :=
    fun _ => borel _
  let : MeasurableSpace (B.unipotentRadical F.Carrier) := borel _
  let : BorelSpace (B.unipotentRadical F.Carrier) := ⟨rfl⟩
  intro μ hμ
  let : ∀ ij : B.UpperPair,
      BorelSpace (Matrix (Fin (B.size ij.1.1)) (Fin (B.size ij.1.2)) F.Carrier) :=
    fun _ => ⟨rfl⟩
  let : ∀ ij : B.UpperPair,
      SecondCountableTopology
        (Matrix (Fin (B.size ij.1.1)) (Fin (B.size ij.1.2)) F.Carrier) :=
    fun ij => inferInstanceAs
      (SecondCountableTopology (Fin (B.size ij.1.1) → Fin (B.size ij.1.2) → F.Carrier))
  let : ∀ ij : B.UpperPair,
      LocallyCompactSpace
        (Matrix (Fin (B.size ij.1.1)) (Fin (B.size ij.1.2)) F.Carrier) :=
    fun ij => inferInstanceAs
      (LocallyCompactSpace (Fin (B.size ij.1.1) → Fin (B.size ij.1.2) → F.Carrier))
  let : ∀ ij, SigmaFinite (μ ij) := fun ij => by
    let := hμ ij
    infer_instance
  exact B.coordinateHaar_of_triangular F.Carrier htri μ

/-- Product additive Haar measure in upper block coordinates is Haar on the radical. -/
theorem glBlockUnipotentCoordinateHaarStatement :
    GLBlockUnipotentCoordinateHaarStatement.{uF} :=
  glBlockUnipotentCoordinateHaarStatement_of_triangular
    HarmonicAnalysis.finiteTriangularTranslation.{0,uF}

end Langlands

import Langlands.Group.GL.BlockUnipotentHaarProof
import Langlands.AllField.Group.GL.BlockUnipotentHaarStatement
import Langlands.AllField.HarmonicAnalysis.PadicScalarHaarScalingProof
open MeasureTheory MeasureTheory.Measure
open scoped BigOperators

namespace Langlands.AllField.GeneralLinear.BlockShape
open Langlands.GeneralLinear.BlockShape
open Langlands.AllField.GeneralLinear.BlockShape
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear

universe u

variable {n : ℕ} (B : BlockShape n) (R : Type u) [CommRing R]

section Measure

variable [TopologicalSpace R] [IsTopologicalRing R] [SecondCountableTopology R]
  [mBlock : ∀ ij : B.UpperPair,
    MeasurableSpace (Matrix (Fin (B.size ij.1.1)) (Fin (B.size ij.1.2)) R)]
  [bBlock : ∀ ij : B.UpperPair,
    BorelSpace (Matrix (Fin (B.size ij.1.1)) (Fin (B.size ij.1.2)) R)]
  [MeasurableSpace (B.unipotentRadical R)] [BorelSpace (B.unipotentRadical R)]

include bBlock

end Measure

end Langlands.AllField.GeneralLinear.BlockShape

namespace Langlands.AllField

universe uF

theorem glBlockUnipotentCoordinateHaarStatement_of_triangular
    (htri : HarmonicAnalysis.FiniteTriangularTranslationStatement.{0,uF}) :
    GLBlockUnipotentCoordinateHaarStatement.{uF} := by
  intro F _ T n B
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.secondCountableTopology
  let : ∀ ij : B.UpperPair,
      MeasurableSpace (Matrix (Fin (B.size ij.1.1)) (Fin (B.size ij.1.2)) F) :=
    fun _ => borel _
  let : MeasurableSpace (B.unipotentRadical F) := borel _
  let : BorelSpace (B.unipotentRadical F) := ⟨rfl⟩
  intro μ hμ
  let : ∀ ij : B.UpperPair,
      BorelSpace (Matrix (Fin (B.size ij.1.1)) (Fin (B.size ij.1.2)) F) :=
    fun _ => ⟨rfl⟩
  let : ∀ ij : B.UpperPair,
      SecondCountableTopology
        (Matrix (Fin (B.size ij.1.1)) (Fin (B.size ij.1.2)) F) :=
    fun ij => inferInstanceAs
      (SecondCountableTopology (Fin (B.size ij.1.1) → Fin (B.size ij.1.2) → F))
  let : ∀ ij : B.UpperPair,
      LocallyCompactSpace
        (Matrix (Fin (B.size ij.1.1)) (Fin (B.size ij.1.2)) F) :=
    fun ij => inferInstanceAs
      (LocallyCompactSpace (Fin (B.size ij.1.1) → Fin (B.size ij.1.2) → F))
  let : ∀ ij, SigmaFinite (μ ij) := fun ij => by
    let := hμ ij
    infer_instance
  exact B.coordinateHaar_of_triangular F htri μ

/-- Product additive Haar measure in upper block coordinates is Haar on the radical. -/
theorem glBlockUnipotentCoordinateHaarStatement :
    GLBlockUnipotentCoordinateHaarStatement.{uF} :=
  glBlockUnipotentCoordinateHaarStatement_of_triangular
    HarmonicAnalysis.finiteTriangularTranslation.{0,uF}

end Langlands.AllField

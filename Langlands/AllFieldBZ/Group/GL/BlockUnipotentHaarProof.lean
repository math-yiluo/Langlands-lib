import Langlands.AllFieldBZ.Group.GL.BlockUnipotentHaarStatement
import Langlands.AllFieldBZ.HarmonicAnalysis.PadicScalarHaarScalingProof
import Langlands.Group.GL.BlockUnipotentHaarProof

/-!
# All-field port of `Langlands.Group.GL.BlockUnipotentHaarProof`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Group.GL.BlockUnipotentHaarProof` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
open MeasureTheory
open MeasureTheory.Measure
open scoped BigOperators
namespace Langlands.AllFieldBZ.GeneralLinear.BlockShape
open Langlands.GeneralLinear.BlockShape
universe u

variable {n : ℕ} (B : Langlands.GeneralLinear.BlockShape n) (R : Type u) [CommRing R]

private theorem _root_.Langlands.GeneralLinear.BlockShape.coordinateCorrection_depends (a : B.unipotentRadical R)
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

end Measure
end Langlands.AllFieldBZ.GeneralLinear.BlockShape
namespace Langlands.AllFieldBZ
universe uF

theorem glBlockUnipotentCoordinateHaarStatement_of_triangular
    (htri : HarmonicAnalysis.FiniteTriangularTranslationStatement.{0,uF}) :
    GLBlockUnipotentCoordinateHaarStatement.{uF} := by
  intro F T n B
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

end Langlands.AllFieldBZ

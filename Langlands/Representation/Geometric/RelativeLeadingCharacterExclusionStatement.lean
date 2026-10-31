import Langlands.Representation.Geometric.GeometricLemmaStatement
import Langlands.Representation.Classification.Tempered
import Langlands.Representation.Twist.LeviRealPower
import Langlands.Group.GL.ReverseBlocks
import Langlands.Representation.Exponents.Jacquet

/-! Leading real-character exclusion on actual reversed geometric pieces. -/

noncomputable section

namespace Langlands

open GeneralLinear Geometric MeasureTheory
open scoped BigOperators

universe uF uV

/-- The leading coarse real part in an actual geometric piece of a real-twisted
tempered source forces its raw minimal representative to be inverse block reversal. -/
def GLRelativeGeometricLeadingCharacterExclusionStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    (n : ℕ) (B : BlockShape n),
    letI := T.topology
    letI := T.leviTopologicalGroup B
    ∀ [MeasurableSpace (B.Levi F.Carrier ⧸ Subgroup.center (B.Levi F.Carrier))]
      [BorelSpace (B.Levi F.Carrier ⧸ Subgroup.center (B.Levi F.Carrier))]
      (μ : Measure (B.Levi F.Carrier ⧸ Subgroup.center (B.Levi F.Carrier)))
      [μ.IsHaarMeasure] (A : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier)),
    IsTemperedModCenter A.representation μ →
    ∀ (t : Fin B.length → ℝ), StrictAnti t →
    ∀ (v : Equiv.Perm (Fin n)), IsMinimalRepresentative B B.reverse v →
    ∀ (S : BlockRefinement B) (R : BlockRefinement B.reverse)
      (hS : sourceLevi F.Carrier B B.reverse v = refinedLevi F.Carrier B S)
      (hR : sourceLevi F.Carrier B.reverse B v⁻¹ = refinedLevi F.Carrier B.reverse R),
    let At := SmoothRep.of (T.leviRealPowerTwist B t A.representation)
      ((T.isSmooth_leviRealPowerTwist_iff B t A.representation).mpr A.isSmooth)
    ∀ (χ : (Fin B.reverse.length → F.Carrierˣ) →* ℂˣ),
    IsGeneralizedEigencharacter
      ((((geometricPieceFunctor T B B.reverse v S R hS hR).obj At).ρ).comp
        (B.reverse.blockScalarLevi F.Carrier)) χ →
    T.IsRealPartOf χ (fun j => (B.reverse.size j : ℝ) * t j.rev) →
    v = B.reversePermutation.symm

end Langlands

import Langlands.Representation.Classification.RelativeJacquetMultiplicityStatement
import Langlands.Representation.Classification.ConstituentRelations
import Langlands.Representation.Exponents.Jacquet

/-!
# Scalar real parts of fine twists of unitary data

An internal interface for the actual flattened block-scalar action of
`fineTwist` at coarse parameter zero. This module states the interface.
-/

namespace Langlands.Exponents

open GeneralLinear Geometric RelativeJacquetMultiplicity

universe uF uV

/-- The negative real determinant twist of irreducible admissible unitary fine
data has a smooth whole-source scalar character with size-weighted real part. -/
def UnitaryFineTwistScalarCharacterStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ) (D : BlockShape n) (R : BlockRefinement D)
      (ω : Rep.{uV} ℂ ((D.flatten R).Levi F.Carrier)),
      Representation.IsIrreducible ω.ρ → IsAdmissible ω.ρ → IsUnitarizable ω.ρ →
      ∀ (v₀ : Fin (D.flatten R).length → ℝ),
        let z : (Fin (D.flatten R).length → F.Carrierˣ) →*
            refinedLevi F.Carrier D R :=
          (flattenedLeviEquiv F.Carrier D R).toMonoidHom.comp
            ((D.flatten R).blockScalarLevi F.Carrier)
        ∃ χ : (Fin (D.flatten R).length → F.Carrierˣ) →* ℂˣ,
          IsOpen (χ.ker : Set (Fin (D.flatten R).length → F.Carrierˣ)) ∧
          Classification.HasScalarCharacter (fineTwist T D R ω v₀ 0).ρ z χ ∧
          T.IsRealPartOf χ (fun k => -(((D.flatten R).size k : ℝ) * v₀ k))

end Langlands.Exponents

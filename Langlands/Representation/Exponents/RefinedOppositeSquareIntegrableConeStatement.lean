import Langlands.Representation.Classification.RelativeRegularComparisonStatement
import Langlands.Representation.Exponents.Chambers
import Langlands.Representation.Geometric.FlattenedLevi
import Langlands.Representation.Parabolic.OppositeRefinementFunctors

/-!
# Strict blockwise cones for opposite exponents of square-integrable product Levis

A smooth generalized character of the actual normalized refined opposite
Jacquet quotient of an irreducible square-integrable product-Levi representation
has its negative scalar real part in the open positive root cone separately
inside every original block. This is a derived analytic statement, without proof.
-/

namespace Langlands.Exponents

open GeneralLinear Geometric

universe uF uV

/-- Strict analytic necessity for every refinement of an actual irreducible
square-integrable product-Levi representation, in scalar real-part coordinates. -/
def RefinedOppositeSquareIntegrableConeStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ (D : BlockShape n)
      (σ : Rep.{uV} ℂ (D.Levi F.Carrier)),
      Representation.IsIrreducible σ.ρ →
      RelativeRegularComparison.IsLeviSquareIntegrable T D σ →
      ∀ (R : BlockRefinement D)
        (χ : (Fin (D.flatten R).length → F.Carrierˣ) →* ℂˣ),
        let z : (Fin (D.flatten R).length → F.Carrierˣ) →* refinedLevi F.Carrier D R :=
          (flattenedLeviEquiv F.Carrier D R).toMonoidHom.comp
            ((D.flatten R).blockScalarLevi F.Carrier)
        IsOpen (χ.ker : Set (Fin (D.flatten R).length → F.Carrierˣ)) →
        IsGeneralizedEigencharacter
          ((T.normalizedRefinedOppositeJacquet D R σ.ρ).comp z) χ →
        ∀ x : Fin (D.flatten R).length → ℝ, T.IsRealPartOf χ x →
          ∀ i : Fin D.length,
            IsPositiveRootCone
              (fun k : Fin (R i).length => -x (D.flattenBlockEquiv R ⟨i, k⟩))

end Langlands.Exponents

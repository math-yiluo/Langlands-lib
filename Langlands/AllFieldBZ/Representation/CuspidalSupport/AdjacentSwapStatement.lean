import Langlands.AllFieldBZ.Representation.CuspidalSupport.AssociationForwardStatement
import Langlands.Representation.CuspidalSupport.AdjacentSwapStatement

/-!
# All-field port of `Langlands.Representation.CuspidalSupport.AdjacentSwapStatement`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.CuspidalSupport.AdjacentSwapStatement` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.CuspidalSupport
open Langlands.CuspidalSupport hiding AdjacentBlockSwapCuspidalInductionFactorsTheorem AssociatedCuspidalInductionFactorsTheorem AssociatedCuspidalInductionHomTheorem CuspidalEmbeddingTheorem CuspidalInductionLengthTheorem TwoBlockAssociatedCuspidalInductionFactorsTheorem
open Langlands.GeneralLinear
universe uF uV uW

/-- A minimal conjugating permutation that exchanges two neighbouring blocks
carries irreducible cuspidal data to normalized inductions with the same
Jordan–Hölder factors, including multiplicities. -/
def AdjacentBlockSwapCuspidalInductionFactorsTheorem : Prop :=
  ∀ (F : LocalFieldPackage.{uF})
    (T : F.TopologicalData) (n : ℕ), 0 < n →
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ (B C : BlockShape n) (w : Equiv.Perm (Fin n))
      (hw : ConjugatesLevi (F := F.Carrier) B C w) (j : ℕ), j + 1 < B.length →
      (∀ a, (Geometric.blockIndex C (w a) : ℕ) =
        Equiv.swap j (j + 1) (Geometric.blockIndex B a : ℕ)) →
      Geometric.IsMinimalRepresentative B C w →
      ∀ (σ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier))
        (τ : SmoothRep.{0, uF, uW} ℂ (C.Levi F.Carrier)),
        σ.IsIrreducible → IsLeviCuspidal B σ.representation →
        τ.IsIrreducible → IsLeviCuspidal C τ.representation →
        Nonempty ((transport B C w hw σ.representation).Equiv τ.representation) →
        HaveSameJordanHolderFactors
          (Rep.of (T.normalizedParabolicInduced B σ.representation))
          (Rep.of (T.normalizedParabolicInduced C τ.representation))

end Langlands.AllFieldBZ.CuspidalSupport

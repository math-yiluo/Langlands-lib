import Langlands.ClassFieldTheory.Local.FiniteComparison

/-! # Finite-to-absolute degree-two inflation and restriction -/

namespace Langlands.ClassFieldTheory.Local

universe u

/-- Finite relative degree-two classes identify with the kernel of absolute
restriction, for K-compatible closure embeddings in characteristic zero. -/
def AbsoluteH2InflationExactness : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K]
    (E : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K E] [IsGalois K E]
    [Algebra (AlgebraicClosure K) (AlgebraicClosure E)]
    [IsScalarTower K (AlgebraicClosure K) (AlgebraicClosure E)],
    Function.Injective (closureInflation K E 2) ∧
      (closureInflation K E 2).range =
        (absoluteRestriction K E 2).hom.toAddMonoidHom.ker

end Langlands.ClassFieldTheory.Local

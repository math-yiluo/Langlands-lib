import Langlands.ClassFieldTheory.Local.FiniteComparison

/-! # Naturality targets for finite-to-absolute inflation -/

namespace Langlands.ClassFieldTheory.Local

universe u

/-- Inflating through a compatible larger finite normal intermediate field
does not change the resulting absolute cohomology class. -/
def ClosureInflationTowerCompatibility : Prop :=
  ∀ (K : Type u) [Field K]
    (L M : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K L] [FiniteDimensional K M]
    [Normal K L] [Normal K M]
    [Algebra L M] [IsScalarTower K L M]
    [IsScalarTower L M (AlgebraicClosure K)]
    (n : ℕ) (x : relativeCohomology K L n),
      closureInflation K M n (relativeInflation K L M n x) =
        closureInflation K L n x

/-- Finite inflation followed by finite base restriction agrees with absolute
restriction when the two embeddings of the source stage into the target closure
agree. The finite base extension need not be Galois. -/
def ClosureInflationBaseChangeCompatibility : Prop :=
  ∀ (K E : Type u) [Field K] [Field E]
    [Algebra K E] [FiniteDimensional K E]
    [Algebra (AlgebraicClosure K) (AlgebraicClosure E)]
    [IsScalarTower K (AlgebraicClosure K) (AlgebraicClosure E)]
    (L : IntermediateField K (AlgebraicClosure K))
    (M : IntermediateField E (AlgebraicClosure E))
    [FiniteDimensional K L] [FiniteDimensional E M]
    [Normal K L] [Normal E M]
    [Algebra K M] [Algebra L M]
    [IsScalarTower K E M] [IsScalarTower K L M],
    (∀ a : L,
      algebraMap M (AlgebraicClosure E) (algebraMap L M a) =
        algebraMap (AlgebraicClosure K) (AlgebraicClosure E)
          (algebraMap L (AlgebraicClosure K) a)) →
    ∀ (n : ℕ) (x : relativeCohomology K L n),
      absoluteRestriction K E n (closureInflation K L n x) =
        closureInflation E M n
          (relativeRestriction K E M n (relativeInflation K L M n x))

end Langlands.ClassFieldTheory.Local

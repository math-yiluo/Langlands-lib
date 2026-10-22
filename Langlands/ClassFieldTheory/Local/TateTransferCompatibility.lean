import Langlands.ClassFieldTheory.Local.TateTransfers
import Langlands.ClassFieldTheory.Local.TateCup

/-! # Fundamental-class cup compatibility with all-integer Tate transfers -/

noncomputable section

namespace Langlands.ClassFieldTheory.Local

universe u v w

section Tower

variable (K : Type v) (L : Type w) (M : Type u)
  [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
  [FiniteDimensional K M] [FiniteDimensional L M]

/-- The fundamental-class cup maps commute with restriction in every Tate degree. -/
def FundamentalClassTateRestriction
    (invKM : relativeCohomology K M 2 →+ RationalModIntegers)
    (invLM : relativeCohomology L M 2 →+ RationalModIntegers) : Prop :=
  ∀ c d, IsFundamentalClass K M invKM c → IsFundamentalClass L M invLM d →
    ∀ (n : ℤ) (x : integralTateCohomology K M n),
      relativeTateRestriction K L M (n + 2) (relativeTateCup K M n c x) =
        relativeTateCup L M n d (integralTateRestriction K L M n x)

/-- The fundamental-class cup maps commute with corestriction in every Tate degree. -/
def FundamentalClassTateCorestriction
    (invKM : relativeCohomology K M 2 →+ RationalModIntegers)
    (invLM : relativeCohomology L M 2 →+ RationalModIntegers) : Prop :=
  ∀ c d, IsFundamentalClass K M invKM c → IsFundamentalClass L M invLM d →
    ∀ (n : ℤ) (x : integralTateCohomology L M n),
      relativeTateCorestriction K L M (n + 2) (relativeTateCup L M n d x) =
        relativeTateCup K M n c (integralTateCorestriction K L M n x)

end Tower

namespace InvariantFamily

/-- Both Tate transfer diagrams for the same raw invariant family, over every
finite Galois upper extension of a tower of p-adic fields. -/
def TateTransferCompatibility {p : ℕ} [Fact p.Prime]
    (I : InvariantFamily.{v,u} p) : Prop :=
  ∀ (F E : PadicField.{v} p) (M : Type u) [Field M]
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    [Algebra F.Carrier M] [Algebra E.Carrier M]
    [IsScalarTower F.Carrier E.Carrier M]
    [FiniteDimensional F.Carrier E.Carrier]
    [FiniteDimensional F.Carrier M] [FiniteDimensional E.Carrier M]
    [IsGalois F.Carrier M] [IsGalois E.Carrier M],
    FundamentalClassTateRestriction F.Carrier E.Carrier M
      (I.relative F M) (I.relative E M) ∧
    FundamentalClassTateCorestriction F.Carrier E.Carrier M
      (I.relative F M) (I.relative E M)

end InvariantFamily

end Langlands.ClassFieldTheory.Local

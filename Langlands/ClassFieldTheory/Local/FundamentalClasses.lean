import Langlands.ClassFieldTheory.Local.Conjugacy
import Mathlib.GroupTheory.OrderOfElement

/-!
# Fundamental-class predicates on actual relative Galois cohomology

The invariant maps here are data, not isomorphisms carrying the desired laws.
A fundamental class is specified by its invariant. No class is chosen.
-/

noncomputable section

namespace Langlands.ClassFieldTheory.Local

universe u v w

section SingleExtension

variable (K : Type v) (L : Type u) [Field K] [Field L]
  [Algebra K L] [FiniteDimensional K L]

/-- The arithmetic-normalized fundamental-class condition in actual relative H².
This predicate does not assert that an invariant map or such a class exists. -/
def IsFundamentalClass
    (inv : relativeCohomology K L 2 →+ RationalModIntegers)
    (c : relativeCohomology K L 2) : Prop :=
  inv c = reciprocalClass (Module.finrank K L)

/-- Existence and uniqueness of the class of invariant `1 / [L : K]`. -/
def HasUniqueFundamentalClass
    (inv : relativeCohomology K L 2 →+ RationalModIntegers) : Prop :=
  ∃! c, IsFundamentalClass K L inv c

/-- A fundamental class has the extension degree as its exact additive order
and generates the actual relative second cohomology group. -/
def FundamentalClassGenerates
    (inv : relativeCohomology K L 2 →+ RationalModIntegers) : Prop :=
  ∀ c, IsFundamentalClass K L inv c →
    addOrderOf c = Module.finrank K L ∧
      AddSubgroup.zmultiples c = ⊤

end SingleExtension

section Tower

variable (K L M : Type u) [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
  [FiniteDimensional K L] [FiniteDimensional K M] [FiniteDimensional L M]

/-- Inflation sends the lower fundamental class to the upper class multiplied
by the upper extension degree. The map is the actual cohomological inflation. -/
def FundamentalClassInflation [Normal K L]
    (invKL : relativeCohomology K L 2 →+ RationalModIntegers)
    (invKM : relativeCohomology K M 2 →+ RationalModIntegers) : Prop :=
  ∀ c d, IsFundamentalClass K L invKL c →
    IsFundamentalClass K M invKM d →
    relativeInflation K L M 2 c = Module.finrank L M • d

/-- Restriction of the base field preserves fundamental classes. -/
def FundamentalClassRestriction
    (invKM : relativeCohomology K M 2 →+ RationalModIntegers)
    (invLM : relativeCohomology L M 2 →+ RationalModIntegers) : Prop :=
  ∀ c d, IsFundamentalClass K M invKM c →
    IsFundamentalClass L M invLM d →
    relativeRestriction K L M 2 c = d

end Tower

section Conjugacy

variable (K : Type v) (K' : Type w) (L L' : Type u)
  [Field K] [Field K'] [Field L] [Field L']
  [Algebra K L] [Algebra K' L']
  [FiniteDimensional K L] [FiniteDimensional K' L']

/-- Transport of a fundamental class by an actual commuting field square.
The induced cohomology isomorphism is constructed in `Conjugacy`, not assumed. -/
def FundamentalClassConjugacy
    (inv : relativeCohomology K L 2 →+ RationalModIntegers)
    (inv' : relativeCohomology K' L' 2 →+ RationalModIntegers)
    (eK : K ≃+* K') (eL : L ≃+* L')
    (h : CompatibleFieldEquivalences eK eL) : Prop :=
  ∀ c d, IsFundamentalClass K L inv c →
    IsFundamentalClass K' L' inv' d →
    (relativeConjugacy eK eL h 2).hom c = d

end Conjugacy

end Langlands.ClassFieldTheory.Local

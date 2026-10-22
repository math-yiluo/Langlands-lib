import Langlands.ClassFieldTheory.Local.FundamentalClasses
import Langlands.ClassFieldTheory.Local.Invariants
import Langlands.ClassFieldTheory.Local.TateNormQuotient
import Langlands.Cohomology.Tate.CupDefinitions

/-! # Cup product with actual relative degree-two Galois classes -/

noncomputable section

namespace Langlands.ClassFieldTheory.Local

universe u v

section Extension

variable (K : Type v) (L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L]

/-- Cup product with an ordinary relative H² class on the left, in every
integer Tate degree, using the actual integral trivial module. -/
def relativeTateCup (n : ℤ) (c : relativeCohomology K L 2) :
    integralTateCohomology K L n →ₗ[IntegerScalars.{u}]
      relativeTateCohomology K L (n + 2) := by
  letI := Fintype.ofFinite Gal(L/K)
  exact Langlands.Tate.integralH2Cup (unitsRepresentation K L) n c

/-- The specialization uses the constructed integral cup operation. -/
theorem relativeTateCup_eq (n : ℤ) (c : relativeCohomology K L 2) :
    letI := Fintype.ofFinite Gal(L/K)
    relativeTateCup K L n c =
      Langlands.Tate.integralH2Cup (unitsRepresentation K L) n c := rfl

/-- Every class with the prescribed arithmetic invariant induces a bijection
in every integer degree. This is a predicate, not an existence assertion. -/
def FundamentalClassTateIsomorphisms
    (inv : relativeCohomology K L 2 →+ RationalModIntegers) : Prop :=
  ∀ c, IsFundamentalClass K L inv c →
    ∀ n : ℤ, Function.Bijective (relativeTateCup K L n c)

variable [IsGalois K L]

/-- The degree-minus-two cup map, with its target identified with the existing
field norm quotient. No inverse or reciprocity isomorphism is assumed. -/
def negativeTwoCupToNormQuotient (c : relativeCohomology K L 2) :
    integralTateCohomology K L (-2) →+
      Additive (Langlands.LocalClassField.NormQuotient K L) :=
  (tateZeroEquivNormQuotient K L).toAddMonoidHom.comp
    (relativeTateCup K L (-2) c).toAddMonoidHom

/-- The norm-quotient presentation has exactly the same bijectivity condition
as the original degree-minus-two cup map. -/
theorem negativeTwoCupToNormQuotient_bijective_iff
    (c : relativeCohomology K L 2) :
    Function.Bijective (negativeTwoCupToNormQuotient K L c) ↔
      Function.Bijective (relativeTateCup K L (-2) c) := by
  exact (tateZeroEquivNormQuotient K L).bijective.of_comp_iff'
    (relativeTateCup K L (-2) c)

end Extension

namespace InvariantFamily

/-- The all-integer fundamental-class cup condition for every finite Galois
extension of every p-adic field, on the same raw invariant family. -/
def TateIsomorphisms {p : ℕ} [Fact p.Prime] (I : InvariantFamily.{u,v} p) : Prop :=
  ∀ (F : PadicField.{u} p) (L : Type v)
    [Field L] [Algebra F.Carrier L] [FiniteDimensional F.Carrier L]
    [IsGalois F.Carrier L],
    FundamentalClassTateIsomorphisms F.Carrier L (I.relative F L)

end InvariantFamily

end Langlands.ClassFieldTheory.Local

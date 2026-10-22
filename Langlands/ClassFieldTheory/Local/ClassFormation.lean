import Langlands.ClassFieldTheory.Local.FiniteInvariantCompatibility
import Langlands.ClassFieldTheory.Local.FundamentalClasses
import Langlands.ClassFieldTheory.Local.MultiplicativeFormation
import Langlands.ClassFieldTheory.Local.Corestriction

/-!
# Relative class-formation and continuous invariant predicates for p-adic fields

All maps in these predicates are actual cohomology maps. The invariant
family has no laws in its type. Finite relative and continuous absolute
cohomology are linked by a genuine diagram, not identified. No fundamental
class is chosen here.
-/

noncomputable section

namespace Langlands.ClassFieldTheory.Local

universe u v w

/-- Corestriction sends the upper-base fundamental class to the lower-base
fundamental class multiplied by the base-extension degree. -/
def FundamentalClassCorestriction
    (K : Type u) (L : Type v) (M : Type w)
    [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional K M] [FiniteDimensional L M]
    (invKM : relativeCohomology K M 2 →+ RationalModIntegers)
    (invLM : relativeCohomology L M 2 →+ RationalModIntegers) : Prop :=
  ∀ c d, IsFundamentalClass L M invLM c →
    IsFundamentalClass K M invKM d →
    relativeCorestriction K L M 2 c = Module.finrank K L • d

/-- The underlying multiplicative formation of any p-adic field. Perfectness
is proved from characteristic zero, not an additional input. -/
def localMultiplicativeFormation {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) :
    FormationData (unitsRepresentation F.Carrier (AlgebraicClosure F.Carrier)) := by
  letI : CharZero F.Carrier :=
    charZero_of_injective_algebraMap (algebraMap (Padic p) F.Carrier).injective
  exact multiplicativeFormation F.Carrier

/-- Serre's axiom I on actual finite relative Galois cohomology. -/
def LocalRelativeH1Vanishing (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (F : PadicField.{u} p) (L : Type v)
    [Field L] [Algebra F.Carrier L] [FiniteDimensional F.Carrier L]
    [IsGalois F.Carrier L],
    Subsingleton (relativeCohomology F.Carrier L 1)

/-- Hilbert 90 for actual continuous cohomology of algebraic-closure units. -/
def LocalAbsoluteH1Vanishing (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ F : PadicField.{u} p, Subsingleton (absoluteCohomology F.Carrier 1)

namespace InvariantFamily

variable {p : ℕ} [Fact p.Prime]

/-- Continuous absolute invariant properties, together with the genuine
finite-stage diagram on every ordinary relative degree-two class. -/
def ContinuousInvariantProperties (I : InvariantFamily.{u,u} p) : Prop :=
  LocalAbsoluteH1Vanishing.{u} p ∧ I.AbsoluteIsomorphisms ∧
    I.AbsoluteRestriction ∧ I.OrdinaryClosureCompatibility

/-- Relative invariants agree along actual inflation maps. -/
def InflationCompatibility (I : InvariantFamily.{u,u} p) : Prop :=
  ∀ (F : PadicField.{u} p) (L M : Type u)
    [Field L] [Field M]
    [Algebra F.Carrier L] [Algebra F.Carrier M] [Algebra L M]
    [IsScalarTower F.Carrier L M]
    [FiniteDimensional F.Carrier L] [FiniteDimensional F.Carrier M]
    [FiniteDimensional L M] [IsGalois F.Carrier L] [IsGalois F.Carrier M],
    ∀ x : relativeCohomology F.Carrier L 2,
      I.relative F M (relativeInflation F.Carrier L M 2 x) = I.relative F L x

/-- Relative restriction multiplies the invariant by the base-extension degree. -/
def RelativeRestriction (I : InvariantFamily.{u,u} p) : Prop :=
  ∀ (F E : PadicField.{u} p) (M : Type u) [Field M]
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    [Algebra F.Carrier M] [Algebra E.Carrier M]
    [IsScalarTower F.Carrier E.Carrier M]
    [FiniteDimensional F.Carrier E.Carrier] [FiniteDimensional F.Carrier M]
    [FiniteDimensional E.Carrier M]
    [IsGalois F.Carrier M] [IsGalois E.Carrier M],
    ∀ x : relativeCohomology F.Carrier M 2,
      I.relative E M (relativeRestriction F.Carrier E.Carrier M 2 x) =
        Module.finrank F.Carrier E.Carrier • I.relative F M x

/-- Relative invariants commute with genuine conjugacy of p-adic extensions. -/
def RelativeConjugacy (I : InvariantFamily.{u,v} p) : Prop :=
  ∀ (F E : PadicField.{u} p) (L M : Type v)
    [Field L] [Field M] [Algebra F.Carrier L] [Algebra E.Carrier M]
    [FiniteDimensional F.Carrier L] [FiniteDimensional E.Carrier M]
    [IsGalois F.Carrier L] [IsGalois E.Carrier M]
    (eF : F.Carrier ≃ₐ[Padic p] E.Carrier) (eL : L ≃+* M)
    (h : CompatibleFieldEquivalences eF.toRingEquiv eL),
    ∀ x : relativeCohomology F.Carrier L 2,
      I.relative E M ((relativeConjugacy eF.toRingEquiv eL h 2).hom x) =
        I.relative F L x

/-- Finite-level form of the class-formation axiom schema: H¹ vanishes,
relative invariant images are the degree torsion subgroups, and actual
inflation and restriction have the required invariant formulas.
Absolute/continuous comparison is a separate predicate, not a type identification. -/
def RelativeClassFormation (I : InvariantFamily.{u,u} p) : Prop :=
  LocalRelativeH1Vanishing.{u,u} p ∧ I.RelativeImages ∧
    I.InflationCompatibility ∧ I.RelativeRestriction

/-- Unique fundamental classes, with their exact order and generation property. -/
def FundamentalClasses (I : InvariantFamily.{u,v} p) : Prop :=
  ∀ (F : PadicField.{u} p) (L : Type v)
    [Field L] [Algebra F.Carrier L] [FiniteDimensional F.Carrier L]
    [IsGalois F.Carrier L],
    HasUniqueFundamentalClass F.Carrier L (I.relative F L) ∧
      FundamentalClassGenerates F.Carrier L (I.relative F L)

/-- Serre's inflation formula for the fundamental classes, quantified without choice. -/
def FundamentalInflation (I : InvariantFamily.{u,u} p) : Prop :=
  ∀ (F : PadicField.{u} p) (L M : Type u)
    [Field L] [Field M]
    [Algebra F.Carrier L] [Algebra F.Carrier M] [Algebra L M]
    [IsScalarTower F.Carrier L M]
    [FiniteDimensional F.Carrier L] [FiniteDimensional F.Carrier M]
    [FiniteDimensional L M] [IsGalois F.Carrier L] [IsGalois F.Carrier M],
    FundamentalClassInflation F.Carrier L M (I.relative F L) (I.relative F M)

/-- Serre's restriction formula for the fundamental classes, quantified without choice. -/
def FundamentalRestriction (I : InvariantFamily.{u,u} p) : Prop :=
  ∀ (F E : PadicField.{u} p) (M : Type u) [Field M]
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    [Algebra F.Carrier M] [Algebra E.Carrier M]
    [IsScalarTower F.Carrier E.Carrier M]
    [FiniteDimensional F.Carrier E.Carrier] [FiniteDimensional F.Carrier M]
    [FiniteDimensional E.Carrier M]
    [IsGalois F.Carrier M] [IsGalois E.Carrier M],
    FundamentalClassRestriction F.Carrier E.Carrier M (I.relative F M) (I.relative E M)

/-- Serre's corestriction formula for the fundamental classes, using the
constructed positive-degree corestriction and no chosen class. -/
def FundamentalCorestriction (I : InvariantFamily.{u,v} p) : Prop :=
  ∀ (F E : PadicField.{u} p) (M : Type v) [Field M]
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    [Algebra F.Carrier M] [Algebra E.Carrier M]
    [IsScalarTower F.Carrier E.Carrier M]
    [FiniteDimensional F.Carrier E.Carrier] [FiniteDimensional F.Carrier M]
    [FiniteDimensional E.Carrier M]
    [IsGalois F.Carrier M] [IsGalois E.Carrier M],
    FundamentalClassCorestriction F.Carrier E.Carrier M
      (I.relative F M) (I.relative E M)

/-- Serre's conjugacy formula for the fundamental classes, quantified without choice. -/
def FundamentalConjugacy (I : InvariantFamily.{u,v} p) : Prop :=
  ∀ (F E : PadicField.{u} p) (L M : Type v)
    [Field L] [Field M] [Algebra F.Carrier L] [Algebra E.Carrier M]
    [FiniteDimensional F.Carrier L] [FiniteDimensional E.Carrier M]
    [IsGalois F.Carrier L] [IsGalois E.Carrier M]
    (eF : F.Carrier ≃ₐ[Padic p] E.Carrier) (eL : L ≃+* M)
    (h : CompatibleFieldEquivalences eF.toRingEquiv eL),
    FundamentalClassConjugacy F.Carrier E.Carrier L M
      (I.relative F L) (I.relative E M) eF.toRingEquiv eL h

end InvariantFamily

end Langlands.ClassFieldTheory.Local

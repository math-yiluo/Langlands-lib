import Langlands.ClassFieldTheory.Local.CyclicClass
import Langlands.LocalField.Canonical
import Langlands.LocalField.Normalization.Definitions
import Langlands.Galois.Local.SpectralDefinitions

/-! # Data and arithmetic normalization for local invariant families

The data below do not assert existence, bijectivity, or compatibility.
Those properties are predicates on the actual cohomology maps.
-/

noncomputable section

namespace Langlands.ClassFieldTheory.Local

universe u v

/-- Candidate maps on actual absolute and finite relative `H²`, with no laws assumed. -/
structure InvariantFamily (p : ℕ) [Fact p.Prime] where
  absolute : ∀ (F : PadicField.{u} p),
    absoluteCohomology F.Carrier 2 →+ RationalModIntegers
  relative : ∀ (F : PadicField.{u} p) (L : Type v)
    [Field L] [Algebra F.Carrier L] [FiniteDimensional F.Carrier L]
    [IsGalois F.Carrier L],
    relativeCohomology F.Carrier L 2 →+ RationalModIntegers

namespace InvariantFamily

variable {p : ℕ} [Fact p.Prime]

/-- The actual absolute invariant maps are group isomorphisms. -/
def AbsoluteIsomorphisms (I : InvariantFamily.{u,v} p) : Prop :=
  ∀ F : PadicField.{u} p, Function.Bijective (I.absolute F)

/-- Finite relative invariants identify `H²` with the actual denominator subgroup. -/
def RelativeImages (I : InvariantFamily.{u,v} p) : Prop :=
  ∀ (F : PadicField.{u} p) (L : Type v)
    [Field L] [Algebra F.Carrier L] [FiniteDimensional F.Carrier L]
    [IsGalois F.Carrier L],
    Function.Injective (I.relative F L) ∧
      (I.relative F L).range = denominatorSubgroup (Module.finrank F.Carrier L)

end InvariantFamily

/-- A cyclic coordinate whose positive generator is the actual arithmetic
residue Frobenius, and whose residue action has trivial inertia. -/
def IsArithmeticUnramifiedCoordinate {p : ℕ} [Fact p.Prime]
    (F : PadicField.{u} p) (L : Type v)
    [Field L] [Algebra F.Carrier L] [FiniteDimensional F.Carrier L]
    {n : ℕ} [NeZero n] (χ : Gal(L/F.Carrier) ≃* Multiplicative (ZMod n)) : Prop :=
  letI := F.canonicalNormedField
  letI := F.canonicalNormedAlgebra
  letI : IsUltrametricDist F.Carrier :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
      (isNonarchimedean_spectralNorm (K := Padic p) (L := F.Carrier))
  letI : ProperSpace F.Carrier := FiniteDimensional.proper (Padic p) F.Carrier
  Function.Injective (LocalGalois.residueHom F.Carrier L) ∧
    ∀ x : IsLocalRing.ResidueField (LocalGalois.extensionIntegers F.Carrier L),
      LocalGalois.residueHom F.Carrier L (χ.symm (Multiplicative.ofAdd 1)) x =
        x ^ Nat.card (IsLocalRing.ResidueField (LocalGalois.baseIntegers F.Carrier))

namespace InvariantFamily

variable {p : ℕ} [Fact p.Prime]

/-- Arithmetic normalization tested on genuine cyclic classes and uniformizers. -/
def ArithmeticNormalization (I : InvariantFamily.{u,v} p) : Prop :=
  ∀ (F : PadicField.{u} p) (L : Type v)
    [Field L] [Algebra F.Carrier L] [FiniteDimensional F.Carrier L]
    [IsGalois F.Carrier L] (n : ℕ) [NeZero n]
    (χ : Gal(L/F.Carrier) ≃* Multiplicative (ZMod n)),
    IsArithmeticUnramifiedCoordinate F L χ →
      ∀ a : F.Carrierˣ, F.canonicalTopologicalData.ord (a : F.Carrier) = 1 →
        I.relative F L (cyclicClass F.Carrier L χ.toMonoidHom a) = reciprocalClass n

/-- Restriction of actual continuous absolute `H²` multiplies invariant by degree.
The algebras on the closures specify the map, rather than an arbitrary homomorphism. -/
def AbsoluteRestriction (I : InvariantFamily.{u,v} p) : Prop :=
  ∀ (F E : PadicField.{u} p) [Algebra F.Carrier E.Carrier]
    [IsScalarTower (Padic p) F.Carrier E.Carrier]
    [FiniteDimensional F.Carrier E.Carrier]
    [Algebra (AlgebraicClosure F.Carrier) (AlgebraicClosure E.Carrier)]
    [IsScalarTower F.Carrier (AlgebraicClosure F.Carrier) (AlgebraicClosure E.Carrier)],
    ∀ x : absoluteCohomology F.Carrier 2,
      I.absolute E (absoluteRestriction F.Carrier E.Carrier 2 x) =
        Module.finrank F.Carrier E.Carrier • I.absolute F x

end InvariantFamily

end Langlands.ClassFieldTheory.Local

import Langlands.Correspondence.SupercuspidalSpecification
import Langlands.LocalFactor.Ramification.InertiaPresentation
import Langlands.Representation.Classification.SupercuspidalStrata
import Langlands.VirtualRepresentation.Weil.Local
import Langlands.VirtualRepresentation.Weil.Twist
import Langlands.VirtualRepresentation.Supercuspidal.Unramified

/-!
# Henniart's numerical correspondence: conductors, unramified twists and orbit counts

Henniart (1988), Théorème 1.2, printed page 498: an injection from irreducible
`n`-dimensional Weil classes to supercuspidal classes of `GL_n(F)` that preserves
conductors and commutes with unramified twists is a bijection. The rank is written
`k + 1`. Sufficient finite counts are stated for unramified-twist orbit strata of
fixed rank and conductor. Proposition definitions only.
-/

noncomputable section

namespace Langlands.Henniart

universe uK uW uV

namespace Numerical

open Langlands.Correspondence Langlands.VirtualRepresentation

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)

/-- `a` is the Artin conductor exponent of `σ`, computed for a representative at
an actual finite inertia presentation with surjective inertia restriction. -/
def HasArtinConductor {k : ℕ} (σ : IrreducibleWeilClass.{uK, uW} K k.succPNat)
    (a : ℕ) : Prop :=
  ∃ (A : FiniteRepresentation.{0, uK, uW} ℂ (Weil.Local.localWeilGroup K))
    (P : Ramification.Padic.FiniteInertiaPresentation K A)
    (hsurj : Function.Surjective (Ramification.Padic.weilInertiaRestriction K P.extension)),
    FiniteRepresentation.classOf A = weilClassForget K σ ∧ P.artinConductor hsurj = (a : ℚ)

/-- The conductor of a supercuspidal class of `GL_(k+1)`: its first level with a
nonzero vector fixed by the last-row congruence subgroup (JPSS 1981, §5). -/
def conductor {k : ℕ} (π : SupercuspidalAutomorphicClass.{uK, uV} K k.succPNat) :
    WithTop ℕ :=
  letI := K.canonicalTopologicalData.topology
  letI := K.canonicalTopologicalData.valuativeRel
  GeneralLinear.SupercuspidalClass.firstFixedLevel (n := k) π

/-- Twist by the unramified character of the Weil group sending geometric
Frobenius to `z`. -/
def weilUnramifiedTwist (k : ℕ) (z : ℂˣ) :
    IrreducibleWeilClass.{uK, uW} K k.succPNat ≃ IrreducibleWeilClass.{uK, uW} K k.succPNat :=
  FiniteRepresentation.continuousIrreducibleTwistEquiv
    (Weil.Local.unramifiedCharacter (Weil.Local.localDegree K) z) (k + 1)

/-- Twist by `g ↦ z ^ ord(det g)`, the unramified character sending a
uniformizer to `z`, composed with the determinant. -/
def supercuspidalUnramifiedTwist (k : ℕ) (z : ℂˣ) :
    SupercuspidalAutomorphicClass.{uK, uV} K k.succPNat ≃
      SupercuspidalAutomorphicClass.{uK, uV} K k.succPNat :=
  letI := K.canonicalTopologicalData.topology
  Supercuspidal.twistClassEquiv
    (K.canonicalTopologicalData.determinantUnramifiedCharacter (k + 1) z)
    (K.canonicalTopologicalData.isOpen_ker_determinantUnramifiedCharacter (k + 1) z)
    (K.canonicalTopologicalData.ker_determinant_le_ker_determinantUnramifiedCharacter (k + 1) z)

/-- Henniart's structured injection in rank `k + 1`: injective, conductor
preserving, and compatible with unramified twists. -/
def IsNumericalInjection {k : ℕ}
    (φ : IrreducibleWeilClass.{uK, uW} K k.succPNat →
      SupercuspidalAutomorphicClass.{uK, uV} K k.succPNat) : Prop :=
  Function.Injective φ ∧
    (∀ (σ : IrreducibleWeilClass.{uK, uW} K k.succPNat) (a : ℕ),
      HasArtinConductor K σ a → conductor K (φ σ) = a) ∧
    ∀ (z : ℂˣ) (σ : IrreducibleWeilClass.{uK, uW} K k.succPNat),
      φ (weilUnramifiedTwist K k z σ) = supercuspidalUnramifiedTwist K k z (φ σ)

/-- Unramified-twist orbits of rank-`k + 1` Weil classes containing a class of
Artin conductor `a`. -/
def weilOrbitStratum (k a : ℕ) :
    Set (Weil.UnramifiedOrbitClasses.{uK, uW} (Weil.Local.localDegree K)) :=
  {c | ∃ σ : IrreducibleWeilClass.{uK, uW} K k.succPNat,
    Weil.unramifiedOrbitClass (Weil.Local.localDegree K) ⟨k.succPNat, σ⟩ = c ∧
      HasArtinConductor K σ a}

/-- Unramified-twist orbits of supercuspidal classes of `GL_(k+1)` containing a
class of conductor `a`. -/
def supercuspidalOrbitStratum (k a : ℕ) :
    Set (PadicSupercuspidal.UnramifiedOrbitClasses.{uK, uV} K) :=
  {c | ∃ π : SupercuspidalAutomorphicClass.{uK, uV} K k.succPNat,
    PadicSupercuspidal.unramifiedOrbitClass K ⟨k.succPNat, π⟩ = c ∧
      conductor K π = (a : WithTop ℕ)}

end Numerical

open Numerical Correspondence

/-- Henniart (1988), Théorème 1.2, first assertion: in every rank there is an
injection preserving conductors and compatible with unramified twists. -/
def NumericalInjectionExistenceStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p) (k : ℕ),
    ∃ φ : IrreducibleWeilClass.{uK, uW} K k.succPNat →
        SupercuspidalAutomorphicClass.{uK, uV} K k.succPNat,
      IsNumericalInjection K φ

/-- Henniart (1988), Théorème 1.2, second assertion: every such injection is
surjective, hence bijective. -/
def NumericalSurjectivityStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p) (k : ℕ)
    (φ : IrreducibleWeilClass.{uK, uW} K k.succPNat →
      SupercuspidalAutomorphicClass.{uK, uV} K k.succPNat),
    IsNumericalInjection K φ → Function.Surjective φ

/-- Finite equal counts: for each rank and conductor, the two sets of
unramified-twist orbits are finite and have the same cardinality. -/
def NumericalOrbitCountStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p) (k a : ℕ),
    (weilOrbitStratum.{uK, uW} K k a).Finite ∧
      (supercuspidalOrbitStratum.{uK, uV} K k a).Finite ∧
      (weilOrbitStratum.{uK, uW} K k a).ncard = (supercuspidalOrbitStratum.{uK, uV} K k a).ncard

/-- The finite orbit counts suffice: together with finiteness of every
supercuspidal conductor they give the surjectivity assertion. -/
def NumericalOrbitReductionStatement : Prop :=
  NumericalOrbitCountStatement.{uK, uW, uV} →
    (∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p) (k : ℕ)
      (π : SupercuspidalAutomorphicClass.{uK, uV} K k.succPNat), conductor K π ≠ ⊤) →
    NumericalSurjectivityStatement.{uK, uW, uV}

/-- The numerical theorem family: existence, surjectivity, the finite orbit
counts and the counting reduction. -/
def NumericalCorrespondenceStatement : Prop :=
  NumericalInjectionExistenceStatement.{uK, uW, uV} ∧
    NumericalSurjectivityStatement.{uK, uW, uV} ∧
    NumericalOrbitCountStatement.{uK, uW, uV} ∧
    NumericalOrbitReductionStatement.{uK, uW, uV}

end Langlands.Henniart

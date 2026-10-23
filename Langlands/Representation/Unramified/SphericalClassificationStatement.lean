import Langlands.Representation.Unramified.PrincipalSeries

/-! # Spherical classification obligations for actual normalized principal series -/

noncomputable section

namespace Langlands.Unramified

open Correspondence

universe uF uV uW

local instance sphericalStatementFieldTopology {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance sphericalStatementGeneralLinearTopology {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (n : ℕ) : TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n

/-- Every ordered tuple of nonzero complex values has a spherical irreducible
admissible constituent in its actual normalized principal series. The witness
carrier lives in the field universe, which also contains the inducing carrier. -/
def SphericalConstituentExistenceStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (r : ℕ)
    (z : Fin (r + 1) → ℂˣ),
    ∃ A : AutomorphicObject.{uF, uF} F r.succPNat, IsSphericalConstituent F z A

/-- Spherical constituents of normalized principal series with the same unordered
uniformizer spectrum are genuinely equivalent, including different orderings
and independent representation carrier universes. -/
def SphericalConstituentUniquenessStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (r : ℕ)
    (z w : Fin (r + 1) → ℂˣ),
    Eigenvalues.ofTuple z = Eigenvalues.ofTuple w →
    ∀ (A : AutomorphicObject.{uF, uV} F r.succPNat)
      (B : AutomorphicObject.{uF, uW} F r.succPNat),
      IsSphericalConstituent F z A → IsSphericalConstituent F w B →
      Nonempty (A.obj.representation.Equiv B.obj.representation)

/-- Every actual irreducible admissible spherical representation occurs in an
unramified normalized principal series, and hence has a spectrum in the relation. -/
def SphericalSpectrumExistenceStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (r : ℕ)
    (A : AutomorphicObject.{uF, uV} F r.succPNat),
    fixedVectors A.obj.representation (sphericalSubgroup F r) ≠ ⊥ →
    ∃ s : Eigenvalues (r + 1), HasSphericalSpectrum F A s

/-- The unordered uniformizer spectrum of an actual spherical object is unique,
with every repeated eigenvalue retained. -/
def SphericalSpectrumUniquenessStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (r : ℕ)
    (A : AutomorphicObject.{uF, uV} F r.succPNat) (s t : Eigenvalues (r + 1)),
    HasSphericalSpectrum F A s → HasSphericalSpectrum F A t → s = t

/-- The actual spherical fixed-vector space of an irreducible admissible object,
when nonzero, has complex dimension exactly one. -/
def SphericalFixedLineStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (r : ℕ)
    (A : AutomorphicObject.{uF, uV} F r.succPNat),
    fixedVectors A.obj.representation (sphericalSubgroup F r) ≠ ⊥ →
    Module.finrank ℂ (fixedVectors A.obj.representation (sphericalSubgroup F r)) = 1

/-- The separate existence, uniqueness, exhaustion and fixed-line obligations.
This is a proposition to prove, not a structure assumed by the constructions. -/
def SphericalPrincipalSeriesStatement : Prop :=
  SphericalConstituentExistenceStatement.{uF} ∧
    SphericalConstituentUniquenessStatement.{uF, uV, uW} ∧
    SphericalSpectrumExistenceStatement.{uF, uV} ∧
    SphericalSpectrumUniquenessStatement.{uF, uV} ∧
    SphericalFixedLineStatement.{uF, uV}

end Langlands.Unramified

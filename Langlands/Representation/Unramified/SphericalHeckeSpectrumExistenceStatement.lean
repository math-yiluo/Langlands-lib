import Langlands.Representation.Unramified.HeckeOperators

/-! # Existence of a spectrum for the actual standard spherical Hecke operators -/

namespace Langlands.Unramified

open Correspondence

universe uF uV

attribute [local instance] heckeFieldTopology heckeGeneralLinearTopology

/-- Every actual irreducible admissible spherical representation has a multiset
of nonzero complex values realizing all its standard Hecke scalars. This is a
separate obligation from realization as a principal-series subquotient. -/
def SphericalHeckeSpectrumExistenceStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (r : ℕ)
    (A : AutomorphicObject.{uF, uV} F r.succPNat),
    fixedVectors A.obj.representation (sphericalSubgroup F r) ≠ ⊥ →
    ∃ s : Eigenvalues (r + 1), HasSphericalHeckeSpectrum F A s

end Langlands.Unramified

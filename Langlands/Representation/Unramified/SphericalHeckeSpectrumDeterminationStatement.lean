import Langlands.Representation.Unramified.HeckeOperators

/-! # Standard spherical Hecke scalars determine the representation -/

namespace Langlands.Unramified

open Correspondence

universe uF uV uW

attribute [local instance] heckeFieldTopology heckeGeneralLinearTopology

/-- Two actual irreducible admissible spherical objects, with independent carrier
universes, whose standard Hecke operators act by the scalars of one common multiset
are equivalent. -/
def SphericalHeckeSpectrumDeterminationStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (r : ℕ)
    (A : AutomorphicObject.{uF, uV} F r.succPNat) (B : AutomorphicObject.{uF, uW} F r.succPNat)
    (s : Eigenvalues (r + 1)),
    HasSphericalHeckeSpectrum F A s → HasSphericalHeckeSpectrum F B s →
      Nonempty (A.obj.representation.Equiv B.obj.representation)

end Langlands.Unramified

import Langlands.Correspondence.HenniartNumericalStatement

/-!
# Finiteness of the supercuspidal unramified-orbit strata

For a p-adic field `K`, a rank `k + 1` and a conductor exponent `a`, only finitely
many unramified-twist orbits of supercuspidal classes of `GL_(k+1)(K)` contain a class
of conductor `a`. This is the supercuspidal finiteness conjunct of the published
`Langlands.Henniart.NumericalOrbitCountStatement`. Proposition definition only.
-/

namespace Langlands.Henniart

universe uK uV

open Numerical

/-- For every p-adic field `K`, rank `k + 1` and conductor exponent `a`, the set
`Numerical.supercuspidalOrbitStratum K k a` of unramified-twist orbits of supercuspidal
classes of `GL_(k+1)(K)` containing a class of conductor `a` is finite. -/
def SupercuspidalOrbitStratumFinitenessStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p) (k a : ℕ),
    (supercuspidalOrbitStratum.{uK, uV} K k a).Finite

end Langlands.Henniart

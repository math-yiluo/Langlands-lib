import Langlands.Correspondence.HenniartNumericalStatement

/-! # Lower bound by rank for the conductor of a supercuspidal class

An irreducible supercuspidal representation of `GL_N(K)`, `N ≥ 2`, over a `p`-adic field `K`
has conductor at least `N`. The rank is written `N = k + 2`, and the conductor is the first
fixed level `Henniart.Numerical.conductor`. Depth zero is included. Bushnell (1987),
Theorem 3 and §5, (5.1)(ii) and (iv), printed pp. 198 and 208; Bushnell–Fröhlich (1985),
(3.3.8)(iv), printed p. 258. Proposition definition only.
-/

namespace Langlands.BushnellKutzko

/-- For every prime `p`, every `K : PadicField p`, every `k : ℕ` and every irreducible
supercuspidal class `π` of `GL_{k+2}(K)`, the first fixed level
`Henniart.Numerical.conductor K π ∈ WithTop ℕ` is at least `k + 2`: the conductor of a
supercuspidal representation of rank `N ≥ 2` is at least `N`. Bushnell (1987), Theorem 3 and
(5.1)(ii), (iv): the normalized Godement–Jacquet exponent is `N (1 + j / e)` with `j ≥ 0`. -/
def SupercuspidalConductorRankLowerBoundStatement.{uK, uV} : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p) (k : ℕ)
    (π : Correspondence.SupercuspidalAutomorphicClass.{uK, uV} K (k + 1).succPNat),
    ((k + 2 : ℕ) : WithTop ℕ) ≤ Henniart.Numerical.conductor K π

end Langlands.BushnellKutzko

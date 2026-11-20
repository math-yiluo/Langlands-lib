# Recovery of torus maps on unbounded torsion orders

The actual torsion subgroups of unbounded orders determine a homomorphism
from a relative torus to a separated group scheme. On a split affine
chart, the free character lattice ensures that every nonzero element of
the group algebra remains nonzero modulo the character quotients for
sufficiently large orders. Closed subschemes containing the indicated
torsion points therefore contain the whole torus. This condition descends
from affine charts and the étale splitting cover. The relative equalizer
of two maps to a separated target is such a closed subscheme.

`TorusTorsionTowerRecoveryStatement.{u}` takes a complete noetherian local
ring `A` with maximal ideal `m`, an actual relative torus `H` and a
separated group scheme `G` over `Spec A`, and a compatible Hom system on
`Spec(A/m^(d+1))` for `d ≥ 0`. For any natural number `q > 1`, a supplied
homomorphism `H ⟶ G` gives the specified system exactly when its restriction
to `H[q^k]` is the unique lift of the formal `q^k`-torsion restriction
for every `k ≥ 0`. These finite-source lifts use completeness for the
maximal-ideal filtration.
This is the torsion determination step used in SGA 3, Exposé XV,
Proposition 4.3, Gille–Polo recomposition, PDF p. 28.

# Invariants of the actual generated field

Source and purpose: Bushnell–Kutzko, *The admissible dual of GL(N) via compact
open subgroups* (1993), `bushnell-kutzko-1993-admissible-dual-gln`,
(2.1.4)(iii), printed p. 50, and (2.4.1)(i), printed p. 65
(PDF pp. 62, 77). These use `e(E|F)`, `f(E|F)` and `[E:F]`.
This module supplies auxiliary constructions on the generated fields
already used in the definitions of pure and simple strata.

`subfieldResidueDegree F E` is the natural-number value of
`Module.length 𝒪[F] (subfieldResidueRing F E)`.
For a finite extension of local fields, the residue ring is `k_E`;
the `𝔬_F`-action factors through its residue field `k_F`.
Its `𝔬_F`-submodules are therefore exactly its `k_F`-subspaces,
and its finite module length is `dim_{k_F} k_E = f(E|F)`.
Using length constructs the invariant directly from the published
integer ring and maximal ideal without supplying a separate residue
field algebra structure. As with `Module.finrank`, the natural value
is zero when the extended length is infinite; that case is unused
in the finite-extension statements.

`elementRamificationIndex F β` and `elementResidueDegree F β`
apply the existing `subfieldRamificationIndex` and the above residue
degree to `elementAlgebra β = F[β]`, with the field structure obtained
from `IsField.toField`. These are total functions, with value zero
when the generated algebra is not a field. All uses in T5–T7
concern pure or simple strata, where it is a field.

`elementDegree F β` is `Module.finrank F (elementAlgebra β)`,
the dimension of the actual generated algebra over `F`.
It is `[F[β]:F]` for a pure stratum.

These constructions are derived notation for the source's usual
extension invariants. No equality, divisibility, minimal-degree
property or other conclusion of T5–T7 is a parameter or hypothesis.

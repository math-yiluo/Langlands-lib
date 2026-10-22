# Index and transitivity laws for actual ordinary corestriction

These proposition definitions concern the independently constructed
`Langlands.Tate.ordinaryCohomologyCorestriction`, on Mathlib's actual
`groupCohomology`. They are targets for proof, not proofs or assumed laws.

All groups and coefficient carriers use an arbitrary common universe `u`.
The coefficient ring is any commutative ring. The ambient group is finite,
and the statements explicitly quantify the finite instances for its subgroups
and coset spaces. Every natural degree is included, in particular degree zero.
There are no topology, trivial-action, or transfer-coherence hypotheses.

`OrdinaryCorestrictionIndex` states

\[
  \operatorname{Cor}_H^G\circ\operatorname{Res}_H^G
      =[G:H]\,\mathrm{id}_{H^q(G,A)}.
\]

Restriction is the actual `groupCohomology.map` for subgroup inclusion and the
identity coefficient map. The right side uses natural-number scalar
multiplication on the module-category morphism, so it is exactly repeated
addition, including for arbitrary characteristic.

For `K ≤ H ≤ G`, `OrdinaryCorestrictionTower` states that direct corestriction
from `K` to `G` equals corestriction first from `K` to `H` and then from `H` to
`G`. It includes the actual change of subgroup coordinates: first apply
`groupCohomology.map` for the equivalence `K.subgroupOf H → K` and the published
`Langlands.Tate.towerCoefficientIso`. That coefficient isomorphism is the identity
on `A`, with the two restricted actions explicitly identified. This gives a map
from cohomology of `K` to cohomology of the nested subgroup before applying
the two transfers.

`OrdinaryTransferLaws` is the conjunction of these exact targets. Coefficient
naturality is separate work in the ordinary-comparison proof task and is not
repeated here. Continuous transfer and its laws remain downstream.

The provenance is derived from Serre, *Local Fields*, 1979 English translation,
Chapter VII section 7, printed page 119 (PDF page 125). Serre defines degree-zero
corestriction by the sum over left cosets, extends it uniquely to cohomology,
and states the index identity in Proposition 6. Transitivity is not quoted
there as a separate proposition: it follows from composition of the two coset
sums in degree zero and uniqueness of the extension. The Lean target uses
the Library's explicit standard-resolution transfer, so proving these targets
must establish the identities for that constructed map, including the
coordinate transport and degree zero. Restricting to finite ambient groups
is sufficient for the intended finite-quotient continuous application.

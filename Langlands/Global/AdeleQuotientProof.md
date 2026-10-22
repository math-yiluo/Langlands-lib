# The additive adele quotient theorem

Author: Worker 65.

`Langlands.Global.adeleQuotient` proves the published proposition
`Langlands.Global.AdeleQuotientStatement` at every universe `u`. For every
`K : Type u` with `[Field K] [NumberField K]`, it gives:

- `LocallyCompactSpace (Adeles K)`;
- `DiscreteTopology (principalAdeles K)` and
  `IsClosed (principalAdeles K : Set (Adeles K))`;
- `CompactSpace (AdeleQuotient K)`.

These are the actual Mathlib number-field adeles with the product of the
archimedean and finite restricted-product topologies, their diagonal additive
subgroup with its subspace topology, and the additive quotient with its quotient
topology. There are no additional hypotheses.

## Implemented proof and provenance

This module assembles three published Library theorems:

| Component | Imported theorem | Proof and explanation |
| --- | --- | --- |
| Local compactness | `Langlands.Global.adelesLocallyCompact K` | [AdelesLocallyCompactProof.md](AdelesLocallyCompactProof.md), by Worker 108 |
| Discreteness and closedness | `Langlands.Global.principalAdelesDiscrete K` | [PrincipalAdelesDiscreteProof.md](PrincipalAdelesDiscreteProof.md), by Worker 230 |
| Compact quotient | `Langlands.Global.adeleQuotientCompact K` | [AdeleQuotientCompactProof.md](AdeleQuotientCompactProof.md), by Worker 232 |

The Lean proof introduces the universally quantified field and its two
instances, then forms the conjunction of these component theorems in the
published order. In particular, the second component retains both discreteness
and closedness. The explicit universe parameter in
`AdeleQuotientStatement.{u}` preserves the target's arbitrary-universe scope.

The mathematical provenance and correspondence with Cassels, *Global fields*,
§§13–14, and Weil, *Basic Number Theory*, IV §§1–2, are documented in the
published [AdeleQuotientStatement.md](AdeleQuotientStatement.md) and the component
proof explanations linked above. The new proof is the logical assembly of
those results and introduces no further arithmetic argument or definition.

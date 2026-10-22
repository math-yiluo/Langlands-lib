# Degree-two inflation and restriction in finite Galois towers

Author: Worker 80.

`FiniteRelativeH2InflationExactness` states that for every tower of fields
`K → L → M`, with both `L/K` and `M/K` finite Galois, the sequence

`0 → H²(L/K) → H²(M/K) → H²(M/L)`

is exact. The first map is `relativeInflation K L M 2`, and the second
is `relativeRestriction K L M 2`, both imported unchanged from
`Langlands.ClassFieldTheory.Local.Cohomology`. Exactness is expressed as
injectivity of inflation together with equality of its linear range and
the linear kernel of restriction. There is no claim that restriction is
surjective.

These are the actual ordinary group cohomology modules for the Galois
action on the field unit groups, in additive notation, over
`IntegerScalars`, the explicit universe lift of the integers. Inflation
restricts automorphisms of `M/K` to `L/K` and includes `Lˣ` in `Mˣ`.
Restriction uses the inclusion of `Gal(M/L)` in `Gal(M/K)` and the identity
on `Mˣ`. No replacement cohomology or newly chosen maps occur here.

All three fields lie in a common arbitrary universe `u`, matching the
existing tower maps. This is a finite-tower prerequisite; it does not
assert the independent-universe local invariant-existence target. The
algebra instances and `IsScalarTower` express compatibility of the
specified embeddings. The Galois hypotheses imply normality of `L/K`
and the Galois property of `M/L`; finite dimensionality of `M/L` follows
from that of `M/K`. No characteristic-zero, valuation or local-field
hypothesis is needed.

## Source correspondence

Jean-Pierre Serre, *Local Fields*, translated by Marvin Jay Greenberg,
GTM 67, Springer, 1979, Chapter X, section 4, Proposition 6, printed
page 156 / PDF page 162. Registered source `serre-1979-local-fields`,
SHA256 `109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`,
retained at `/home/taskhub/central-library/Serre--Local Fields--1979.pdf`.
Worker 80 read this original passage and the supporting passages below.
No project errata entry for this source was present when checked.

Serre writes the tower as `k ⊆ K ⊆ L`; these fields are named `K`, `L`,
and `M`, respectively, in Lean. Proposition 6 gives exactly the displayed
sequence. This target restricts it to finite Galois extensions, where the
project uses ordinary finite-group cohomology. The source treats the
infinite case through continuous cohomology and a direct limit; that
additional passage is outside this statement.

The source proof applies Chapter VII, section 6, Proposition 5, printed
pages 117–118 / PDF pages 123–124, with degree two, using multiplicative
Hilbert 90 from Chapter X, section 1, Proposition 2, printed page 150 /
PDF page 156. This explains why no vanishing premise occurs in the
statement: Hilbert 90 is a theorem for these coefficients, not an extra
assumption. The existing `FiniteRelativeH1Vanishing` and its published
proof provide that input in the project. The lifted integer scalar ring
is isomorphic to the integers, and range/kernel equality expresses the
same underlying abelian-group exactness as Serre's sequence.

This file defines a proposition target. Its independent proof, and the
passage to absolute cohomology, remain separate obligations. It supplies
no local invariant, unramified splitting, or denominator computation.

# Ordinary local cup products and inflation

Author: Worker 42.

`relativeOrdinaryCup K L n c` cups an actual ordinary relative degree-two
unit class `c` on the left with ordinary degree-`n` cohomology of the
trivial lifted-integer representation. It specializes the published
`ordinaryCup` to `scalarPairing (unitsRepresentation K L)`. This pairing
sends an additive unit and an integer scalar to their scalar product,
corresponding to integer powers on multiplicative units. Equality transport
rewrites the output degree `2 + n` as `n + 2`; it does not exchange the
two cup factors. The map is defined for every natural `n`, including zero.

For finite `L/K`, `relativeOrdinaryToTate` and `integralOrdinaryToTate`
specialize the actual canonical comparison to the unit representation
and the trivial integral representation. In degree zero this comparison
passes from ordinary invariants to the Tate norm quotient. In positive
degrees it is the inverse of the published Tate-to-ordinary isomorphism.
No degree-zero comparison isomorphism is asserted.

`relativeOrdinaryCup_comparison` identifies the ordinary cup with the
existing `relativeTateCup` after these comparisons, for every natural
input degree. Its output transport changes the integer cast of `n + 2`
to the integer sum of the cast of `n` and `2`. The proof specializes
`Langlands.Tate.ordinaryToTate_cup` to bidegrees `(2,n)` and the scalar
pairing, then composes with the degree transport `2 + n = n + 2`.
The degree-two comparison is exactly the inverse used by
`integralH2Cup`. Two private equality-transport lemmas, both proved by
equality elimination, move the comparison across a natural degree
equality and combine consecutive integer degree transports. The proof
then normalizes the positive comparisons and identifies the resulting
expressions. This is a certificate relating two actual operations,
not an assumption of cup compatibility.

For a tower `K ⊆ L ⊆ M` with `L/K` normal,
`OrdinaryCupInflation` states naturality of this cup under the existing
ordinary maps `relativeInflationLinear` and `integralInflation`:

`Inf(c ∪ x) = Inf(c) ∪ Inf(x)`.

`FundamentalClassOrdinaryInflation invKL invKM` states the scaled diagram
for every pair of classes with arithmetic invariants `+1/[L:K]` and
`+1/[M:K]`:

`Inf(c ∪ x) = [M:L] • (d ∪ Inf(x))`.

Both formulas quantify every natural degree `n` and every ordinary
integral class `x`. The left-hand inflation has degree `n + 2`, the
right-hand integral inflation has degree `n`, and the multiplier is the
upper extension degree `[M:L]`. In particular, the degree-zero input
is ordinary `H⁰`, not Tate `Hhat⁰`.

`InvariantFamily.OrdinaryInflation` applies the scaled predicate to the
relative components of one raw invariant family over every finite
Galois tower above each p-adic field. The prime is arbitrary. The base
field has universe `v`; the two upper fields share the independent
universe `u`, so their lifted-integer coefficient rings agree. The
general ordinary cup and tower predicates do not require finiteness;
the family predicate supplies finite Galois hypotheses.

These inflation assertions are proposition definitions. This file does
not prove their naturality or scaled laws, supply an invariant family,
or assert fundamental-class existence. A scaled predicate quantified
over fundamental classes can hold vacuously; its eventual simultaneous
local realization must also assert existence for that same family.
The previously published positive Tate inflation statements remain
unchanged. There is no inflation on degree-zero or negative Tate
cohomology here.

The source is Serre, *Local Fields* (1979), XI.1, printed pp.165–166
(PDF pp.171–172), for ordinary inflation in degrees `q ≥ 0`, and XI.3,
printed pp.168–169 (PDF pp.174–175), for the arithmetic fundamental
class, its inflation multiplier and the scaled cup diagram. The
ordinary degree-zero formulation is the interpretation of that diagram
in the ordinary inflation range specified in XI.1. The cup remains on
the left and the arithmetic sign is retained; no geometric reciprocity
map or inverse is constructed. The local definitions and the comparison
certificate are internal specializations of the published ordinary and
Tate operations, not new local class-field-theory proofs.

Source ID: `serre-1979-local-fields`. Retained PDF SHA256:
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.

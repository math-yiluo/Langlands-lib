# Fundamental-class cup products and Tate transfers

Author: Worker 42.

For a finite field tower `K → L → M`, the two proposition definitions
use the actual unit-valued and integral Tate transfer maps in
`TateTransfers` and the actual left cup operation in `TateCup`.
For every pair of classes `c ∈ H²(M/K)` and `d ∈ H²(M/L)` with
invariants `+1/[M:K]` and `+1/[M:L]`, respectively, and every integer
`n`, they state:

- `FundamentalClassTateRestriction`: `Res(c ∪ x) = d ∪ Res(x)`
  for every integral Tate class `x` for `Gal(M/K)` in degree `n`.
- `FundamentalClassTateCorestriction`: `Cor(d ∪ x) = c ∪ Cor(x)`
  for every integral Tate class `x` for `Gal(M/L)` in degree `n`.

The transfer on the left has unit coefficients and degree `n + 2`;
the transfer on the right has trivial integral coefficients and degree
`n`. Both cup operations have the fundamental class on the left.
There is no degree multiplier in either diagram. In particular, the
corestriction diagram uses the projection formula and restriction of
the upper fundamental class. It is distinct from the separate degree-two
formula `Cor(d) = [L:K] • c`.

The two raw predicates retain independent universes for all three fields.
`InvariantFamily.TateTransferCompatibility I` specializes their conjunction
to all towers of p-adic fields `F → E` and all finite upper fields `M`
Galois over both. The lower fields share arbitrary universe `v`; the
upper field has arbitrary universe `u`, which supplies the lifted integer
scalar ring. No Galoisness of `E/F` is imposed. Both invariant maps are
components of the same raw family `I`.

These are Prop-valued definitions of the compatibility conclusions,
not proofs. They assume no compatibility law or chosen fundamental
classes as data. Since they quantify conditionally over fundamental
classes, they can be vacuous for unsuitable raw invariant maps. A local
realization target must assert existence of one family with invariant
images, fundamental-class existence, and these compatibility properties
simultaneously.

Source: Serre, *Local Fields* (1979), XI.3, printed pp. 168–169
(PDF pp. 174–175), specifically the fundamental-class restriction formula
and the statement that the cup isomorphisms commute with restriction and
corestriction in every integer degree. These predicates translate those
diagrams using the constructed local maps, without assuming or claiming
the class-formation theorem. The positive arithmetic convention is
unchanged; no reciprocity inverse or geometric output inversion occurs
in these cup diagrams. The scaled inflation diagram belongs to the
separate inflation statement.

Source ID: `serre-1979-local-fields`. Retained PDF SHA256:
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.

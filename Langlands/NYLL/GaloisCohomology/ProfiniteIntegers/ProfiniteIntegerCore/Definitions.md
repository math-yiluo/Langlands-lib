# NYLL M008.001–018: profinite-integer closure data

This file ports the actual closure model from Naganori Yamaguchi,
`Nyll/GaloisCohomology/ProfiniteIntegers/ProfiniteIntegerCore.lean`, pinned at
commit `fbd320cd8b1b06487c58227e92eb135794267709`, lines 28–123. The original file
SHA-256 is `a6cdc6d3cfca209257868daa4e1aa09ca4f83d08927114958d2737b93b309ae5`.
The registered collection is `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

`Langlands.NYLL.ClassFormation.ZHat : Type 0` is defined to be the topological
closure of the diagonal image of the ordinary integers in the product of
`ZMod n` over all positive natural moduli. The ambient ring has its product
topology, and the closure has its subspace topology. The construction retains
these concrete subtypes and the source's `def` boundary for `ZHat`.

The commutative ring, topology, continuous ring operations, Hausdorff,
totally disconnected and compact instances are transported from this closure.
Compactness uses the closed embedding of the closure in the product of the
finite discrete residue rings. `zHatProfiniteAddGrp` bundles its additive group;
`zHatMulProfiniteGrp` bundles the same additive group through `Multiplicative`.
In the latter presentation multiplication means addition of profinite integers.

For each explicit `n : ℕ` and `hn : 0 < n`, `zHatReduction n hn` is a
`ContinuousAddMonoidHom ZHat (ZMod n)`. Its value is the coordinate of a closure
point at the index `(n, hn)`. Its zero and addition laws are definitional, and
continuity is coordinate evaluation composed with subtype inclusion. The type,
parameter order, binder explicitness and implementation are retained.

The declaration correspondence is as follows. Public names in the table have
prefix `Langlands.NYLL.ClassFormation`; internal names have prefix
`Langlands.NYLL.PortInternal.M008`.

| Unit | Original declaration and line | Adapted declaration |
| --- | --- | --- |
| M008.001 | private structure `ClassFormation.ZHatIndex`, 28–30 | `d001`, with unchanged `modulus` and `positive` fields |
| M008.002 | private `NeZero i.modulus` instance, 32–33 | `d002` |
| M008.003 | private `ClassFormation.zHatIndex`, 35–36 | `d003` |
| M008.004 | private `ClassFormation.ZHatAmbient`, 38–39 | `d004` |
| M008.005 | private `ClassFormation.zHatDiagonal`, 41–54 | `d005` |
| M008.006 | private `ClassFormation.zHatIntegerSubring`, 56–57 | `d006` |
| M008.007 | private `ClassFormation.ZHatClosureModel`, 59–60 | `d007` |
| M008.008 | `ClassFormation.ZHat`, 67–68 | `ZHat` |
| M008.009 | `CommRing ZHat` instance, 71–73 | `d009` |
| M008.010 | `TopologicalSpace ZHat` instance, 76–78 | `d010` |
| M008.011 | `IsTopologicalRing ZHat` instance, 81–83 | `d011` |
| M008.012 | `T2Space ZHat` instance, 86–88 | `d012` |
| M008.013 | `TotallyDisconnectedSpace ZHat` instance, 91–93 | `d013` |
| M008.014 | `CompactSpace ZHat` instance, 96–98 | `d014` |
| M008.015 | `ClassFormation.zHatProfiniteAddGrp`, 101–102 | `zHatProfiniteAddGrp` |
| M008.016 | `TotallyDisconnectedSpace (Multiplicative ZHat)` instance, 105–107 | `d016` |
| M008.017 | `ClassFormation.zHatMulProfiniteGrp`, 111–112 | `zHatMulProfiniteGrp` |
| M008.018 | `ClassFormation.zHatReduction`, 115–123 | `zHatReduction` |

Worker 120 made these modifications: prefix the public namespace with
`Langlands.NYLL`; replace source-private names and anonymous instance names by
the stable internal names in the table; extract the first eighteen commands;
and omit the unused source import of `TopologicalGeneration`. The four original
Mathlib imports are unchanged. The support is now addressable by later source
proof modules rather than Lean's file-private generated names. Instance bodies
and registration strength are unchanged: none is a local source instance, and
each is on the new index type or on the new `ZHat` presentation. They introduce
no instance for an existing host profinite-integer type. The `ZHat` docstring's
reference to a later representation equivalence is omitted because that
construction is not in this unit. No other mathematical modification is made.

The source's initial commands do not use any M007 declaration. A focused
compilation of this module with the four Mathlib imports verifies that its data
and instances need no `TopologicalGeneration` import. This removes that import
only for M008.001–018; it does not discharge the later topological generation
result.

The current Library already provides
`Langlands.Global.ProfiniteIntegerRing`, through
`Langlands.Global.ResidueLimit.compatibleSubring`, and
`Langlands.Weil.ProfiniteIntegers`, through Mathlib's
`ProfiniteGrp.ProfiniteCompletion.completion`. These are related models: the
first is a subtype cut out by divisibility compatibility equations, and the
second is the inverse limit of finite group quotients of `Multiplicative ℤ`.
Neither is this source's closure subtype, nor does either existing declaration
provide its closure-coordinate implementation. No replacement comparison with
this source model is imported or assumed. Existing Mathlib product, subring
closure and bundled-group infrastructure is reused directly; it is not
reimplemented. Searches found no published `ZHat`, `zHatReduction` or
`ProfiniteIntegerCore` port declaration at the checked Library base.

This is a data contribution. It does not prove the later source targets
M008.019–024: reduction computation, extensionality, transition compatibility,
density of integers, or generation by one. It also makes no identification with
a host profinite completion and establishes no local reciprocity theorem.

The original copyright, Apache-2.0 and author header are retained in Lean.
The retained license and notice are `licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
`licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).

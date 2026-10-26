# Native maximal-ideal adic topology

This module proves the published closed proposition
`Langlands.NYLL.ValuationTheory.Valuations.RankOneDiscreteValuationSubringIsAdicStatement.{u,v}`
as
`Langlands.NYLL.ValuationTheory.Valuations.rankOneDiscreteValuationSubring_isAdic.{u,v}`.
Its complete unapplied theorem type is the named statement. Every mathematical
parameter is quantified inside that statement; the field and value group retain
independent universe levels.

## Target and supplied structures

For every `{K : Type u} [Field K] {Gamma : Type v}
[LinearOrderedCommGroupWithZero Gamma] [Valued K Gamma]` and
`[(Valued.v : Valuation K Gamma).IsRankOneDiscrete]`, put
`val = (Valued.v : Valuation K Gamma)`, `A = val.valuationSubring`, and
`m = IsLocalRing.maximalIdeal A`. The theorem proves `IsAdic m`.
Mathlib defines this as equality of the supplied topology on `A` with its
`m`-adic topology.

The supplied `Valued` uniformity determines the topology on `K`; `A` carries
the native subtype topology. The local `IsTopologicalRing A` instance uses
that existing topology and the canonical subring operations. No topology or
uniformity is replaced. The proof assumes neither completeness nor adicity,
local compactness, finite residue field, Henselianity, surjectivity onto the
ambient value group, or a complete discretely valued field bundle.

## Implemented proof

Choose a uniformizer `pi : A` using
`Valuation.exists_isUniformizer_of_isCyclic_of_nontrivial`.
Rank-one discreteness supplies the cyclic and nontrivial restricted value group
needed by that theorem. For every `x : A` and `n : Nat`, a local calculation
establishes

`x ∈ m ^ n ↔ val (x : K) ≤ val ((pi ^ n : A) : K)`.

It rewrites `m` using `Valuation.IsUniformizer.is_generator` and
`Ideal.span_singleton_pow`, reduces membership to divisibility with
`Ideal.mem_span_singleton`, and applies `Valuation.Integers.dvd_iff_le` to
`Valuation.valuationSubring.integers`. This is the calculation of M107.005,
kept inside the proof rather than exported as another declaration.

Apply Mathlib's `isAdic_iff`. Its first condition says each ideal power is
open. The value of `pi ^ n` is nonzero by the uniformizer property and
`map_pow`. `Valued.isOpen_closedBall` makes the corresponding closed ball
open in `K`. The restriction comparison `val.restrict_le_iff` and the
continuous subtype inclusion pull this ball back to `A`. The local membership
equivalence identifies the preimage with `m ^ n`, including `n = 0`.

For the second condition, take an arbitrary native zero neighborhood in `A`.
`mem_nhds_subtype` gives an ambient zero neighborhood, and
`Valued.hasBasis_nhds_zero` supplies a contained ball of unit radius `gamma`
in the exact restricted group `(MonoidWithZeroHom.ofClass val).ValueGroup₀`.
The order isomorphism
`Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt val` transfers
`MulArchimedean` from `WithZero (Multiplicative Int)` to that restricted group.
The proof installs this derived instance locally. Since the uniformizer has
restricted value less than one, `exists_pow_lt₀` gives `n` with
`val.restrict (pi : K) ^ n < gamma`.
The membership equivalence, restriction comparison and `map_pow` then place
all of `m ^ n` inside the chosen ball and hence inside the original neighborhood.
These are precisely the two conditions required by `isAdic_iff`.

## Source correspondence and imports

The original is Naganori Yamaguchi's
[`Nyll/ValuedFieldTheory/Valuation/ValuedAdicComplete.lean`, lines 49–115](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Valuation/ValuedAdicComplete.lean#L49-L115),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, unit M247.002.
The local ideal-membership calculation corresponds to
[`DiscreteValuationField/Complete.lean`, lines 82–95](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/Complete.lean#L82-L95),
unit M107.005. The proof follows the original uniformizer, open-ball and
neighborhood-cofinality argument.

The direct imports are:

- `Langlands.NYLL.ValuedFieldTheory.Valuation.ValuedAdicComplete.Statements`,
  for the unchanged published target, canonical valuation subring and
  `isAdic_iff`;
- `Mathlib.RingTheory.Valuation.Discrete.RankOne`, for the restricted
  value-group order isomorphism;
- `Mathlib.GroupTheory.ArchimedeanDensely`, for `exists_pow_lt₀`;
- `Mathlib.Topology.Algebra.Valued.ValuedField`, for the topological-ring
  structure of the supplied valued field.

The imported Mathlib valuation-subring, uniformizer, ideal and topology APIs
supply the other results named above. No external repository module is imported.
M247.001 (the DVR result), M247.003 (adic completeness), M247.004
(`CompleteDVF` packaging), and the remaining M107 declarations are not part of
this proof module.

## Attribution and modifications

The original source is registered as
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The original M247 file's SHA256 is
`183b8dd3fb4910ec7378d280839436826d06929fa4e8081dd460e89cbd05d5fb`;
the M107 file's SHA256 is
`509cbb37745761cf3689a905512378e430932d5e8e13988470cbf072d84e46b9`.
Both files were read and their hashes checked. No applicable source erratum
was found in the project, current Library or retained literature lookup.

The original copyright and author header is preserved verbatim. The existing
unmodified [LICENSE](../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../licenses/NYLL/NOTICE) remain applicable; their SHA256
values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

Worker 384 extracted this proof on 26 October 2026, prefixed the namespace with
`Langlands.NYLL`, closed its theorem type over the published statement, selected
the focused imports, inlined the original M107.005 Mathlib calculation as a
local `have`, and wrote this explanation. Worker 25 is an actual coauthor for
the reused P3 compatibility adaptation: the explicit restricted-group type
and local `let` instance for `MulArchimedean`, documented in his
[published P3 compatibility account](../../../../../notes/reuse/nyll-port-feasibility.md#4-compatibility-changes-and-semantic-assessment)
and retained in the
[adapted M247 source](/home/taskhub/pilot/drafts/ece1c58f-95d0-4ad6-9ddd-adb07dc29028/revision-3-2df3e8c2ccf60e3bbabb54ea8c44f8a9ea332e5d97a7fda1fd71fb7484a5c591/files/modified/Nyll/ValuedFieldTheory/Valuation/ValuedAdicComplete.lean.md).
That feasibility source is attribution and adaptation input, not an accepted
mathematical dependency. Worker 106 supplied task and source routing.
The approved environment is Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.

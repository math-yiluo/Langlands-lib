# Native adic topology and completeness of a valuation subring

This module defines exactly two closed proposition targets corresponding to
M247.002 and M247.003 of Naganori Yamaguchi's
[`Nyll/ValuedFieldTheory/Valuation/ValuedAdicComplete.lean`, lines 49–138](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Valuation/ValuedAdicComplete.lean#L49-L138),
at commit `fbd320cd8b1b06487c58227e92eb135794267709`. These definitions name
propositions; they contain no proofs of the propositions. A subsequent proof
must establish the corresponding published target separately.

## Exact source correspondence

Both adapted names belong to `Langlands.NYLL.ValuationTheory.Valuations`.
The source namespace is `ValuationTheory.Valuations`.

| Source theorem | Closed proposition target | Source unit and declaration |
| --- | --- | --- |
| `rankOneDiscreteValuationSubring_isAdic` | `RankOneDiscreteValuationSubringIsAdicStatement` | M247.002, lines 49–56; proof continues through line 115 |
| `rankOneDiscreteValuationSubring_isAdicComplete` | `RankOneDiscreteValuationSubringIsAdicCompleteStatement` | M247.003, lines 120–129; proof continues through line 138 |

The spelling map adds the `Langlands.NYLL` namespace prefix, converts each
theorem's descriptive name to PascalCase, removes the underscore before
`isAdic` or `isAdicComplete`, and appends `Statement`. Each original theorem's
entire parameter telescope is quantified inside the corresponding definition.
Only the independent universe levels `u` and `v` remain declaration parameters:
each complete, unapplied constant has type `Prop`.

## Quantifiers and mathematical meaning

Each body universally quantifies, in source order:
`{K : Type u} [Field K] {Gamma : Type v}
[LinearOrderedCommGroupWithZero Gamma] [Valued K Gamma]
[(Valued.v : _root_.Valuation K Gamma).IsRankOneDiscrete]`.
The second body then quantifies `[CompleteSpace K]`, exactly as the source.
The field and value group can inhabit different universes. The two definitions
add no field, value-group or residue-field restrictions.

For each supplied structure, write `val` for
`(Valued.v : _root_.Valuation K Gamma)`, `A` for `val.valuationSubring`, and
`m` for `IsLocalRing.maximalIdeal A`. The valuation subring is Mathlib's actual
subring of elements `x : K` satisfying `val x ≤ 1`; its commutative-ring and
local-ring structures are the canonical Mathlib structures.

`RankOneDiscreteValuationSubringIsAdicStatement` asserts `IsAdic m`.
Mathlib's `IsAdic` says that the already supplied topology equals
`m.adicTopology`. Here the supplied topology on `A` is the native subtype
topology inherited from `K`. The `Valued K Gamma` instance extends
`UniformSpace K` and `IsUniformAddGroup K`, and its uniform space supplies the
ambient topology. The definition neither selects an adic topology as an
instance nor quantifies an independently chosen topology. Equality with the
adic topology is the conclusion.

`RankOneDiscreteValuationSubringIsAdicCompleteStatement` asserts
`IsAdicComplete m A`. This is Mathlib's algebraic adic-completeness predicate,
combining `IsHausdorff m A` and `IsPrecomplete m A`, with the usual self-module
structure on `A`. Its additional hypothesis `CompleteSpace K` uses precisely
the uniform space inherited from the supplied `Valued K Gamma`. The predicate
`IsAdicComplete` itself does not take a topology or uniformity argument.
No `IsAdic`, `IsAdicComplete`, completeness of `A`, local compactness,
`IsNonarchimedeanLocalField`, finite residue field, Henselianity or
`CompleteDVF` assumption is introduced.

## Mathlib reuse and imports

The direct imports are:

- `Mathlib.RingTheory.AdicCompletion.Topology`, providing `IsAdicComplete`
  through its `Basic` import, `IsAdic` through its `AdicTopology` import,
  and the existing comparison lemma `IsAdic.isAdicComplete_iff`;
- `Mathlib.RingTheory.Valuation.Discrete.Basic`, providing
  `Valuation.IsRankOneDiscrete`, and the valuation-subring/local-ring support;
- `Mathlib.Topology.Algebra.Valued.ValuationTopology`, providing the supplied
  `Valued` structure and its inherited uniformity and topology.

No NYLL module is imported. The source proof imports for archimedean powers,
rank-one comparison, discrete valuation fields and valued-field lemmas are
unnecessary to formulate these targets. Neither M247.001 (the DVR theorem),
M107.005 (the ideal-power comparison), M247.004 (the `CompleteDVF`
construction), nor the separate `IsCompleteDiscrete`/`CompleteDVF` definitions
are dependencies of the two proposition bodies.

The current Library and Mathlib were searched by the original/adapted names
and by valuation-subring/adic terminology. The relevant existing Mathlib
comparison `IsAdic.isAdicComplete_iff` assumes `IsAdic` and connects adic
completeness to `CompleteSpace` and `T2Space`; it does not supply the generic
native-topology assertion. Mathlib's adic-completeness instance in
`NumberTheory.LocalField.Basic` assumes `IsNonarchimedeanLocalField`, so it
is narrower than the supplied rank-one discrete valuation interface here.
These are reusable tools for later proofs, not proofs of these targets.

For provenance, the original M247.002 proof compares neighborhoods with
uniformizer powers in the restricted value group; M247.003 uses closedness
of the valuation subring and `IsAdic.isAdicComplete_iff`. No original proof is
included or claimed as an implemented proof by this statement module. In
particular, the compatibility patch P3 for a local `MulArchimedean` witness
lies inside the omitted original proof and makes no change to these signatures.

## Source record and attribution

The registered source `external-lean-reuse-snapshots-2026-10-21` has content
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
Its local source root is
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The original file's SHA256 is
`183b8dd3fb4910ec7378d280839436826d06929fa4e8081dd460e89cbd05d5fb`.
The attribution supplement `nyll-classfieldtheory-fbd320cd-supplement` has
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable erratum was present in the project or published errata lookup
at extraction time.

The original copyright and author header is retained verbatim: copyright
2026 Naganori Yamaguchi, authors Naganori Yamaguchi (assisted by OpenAI Codex),
released under Apache-2.0. The existing unmodified
[LICENSE](../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../licenses/NYLL/NOTICE) accompany the extraction and
match the pinned originals byte for byte.

Worker 449 independently extracted the original theorem signatures on
25 October 2026, closed their quantifiers inside Prop-valued definitions,
added the namespace prefix and target names, reduced the imports to the
three Mathlib modules above, and wrote this Markdown. The Lean header records
these modifications. No other worker's adapted Lean content was used. The
module targets approved Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`; publishing its propositions
establishes no adic-topology theorem, adic-completeness theorem, reciprocity
normalization or downstream inertia assertion.

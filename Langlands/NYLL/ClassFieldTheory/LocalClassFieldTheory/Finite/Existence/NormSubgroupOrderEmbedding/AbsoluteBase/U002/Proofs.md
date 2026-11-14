# Normality of finite abelian subextensions over the absolute base

This module proves
`Langlands.NYLL.LocalClassFieldTheory.finiteAbelianSubextension_normal_over_absoluteBaseStatement`
from the published `AbsoluteBase.Statements` module, without changing its
statement or data.

The complete theorem telescope is
`(K : Type) [Field K] (L : FiniteAbelianSubextension (intrinsicAbstractBase K))`.
Thus `K` is in universe zero, both `K` and `L` are explicit, and the theorem
type is exactly
`finiteAbelianSubextension_normal_over_absoluteBaseStatement K L`.
The theorem name is
`Langlands.NYLL.LocalClassFieldTheory.finiteAbelianSubextension_normal_over_absoluteBase`.

## Implemented proof

The definition `intrinsicAbstractBase K` is the closed subgroup fixing the
bottom intermediate field in `SeparableClosure K`. The published theorem
`closedFixingSubgroup_bot_eq_baseField K (SeparableClosure K)` identifies it
with `baseField (intrinsicAbsoluteGalois K)`.

For an element `h` of the relative subgroup and a conjugating element `g`
of the abstract base subgroup, the proof constructs representatives `h'`
and `g'` in the intrinsic base subgroup. Membership of `h'` follows from
`L.below` and the hypothesis on `h`; membership of `g'` follows by the
published base equality from `g.property`. The existing normality witness
`L.normal` then supplies the required conjugation membership.

The published abbreviation `extensionSubgroup` is `Subgroup.subgroupOf`.
Consequently its membership, the coercions of `h'` and `g'`, and their
products and inverses reduce definitionally to the ambient group expressions.
The proof uses `change` to expose the hypothesis and closes with
`L.normal.conj_mem h' hh g'`. It introduces no new instance or assumption.
Neither finiteness nor commutativity of the quotient is needed in this
normality transfer.

## Source and modifications

The source is Naganori Yamaguchi's NYLL `ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/NormSubgroupOrderEmbedding.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/NormSubgroupOrderEmbedding.lean),
unit M300.002, lines 48–75. Source lines 1–100, including the complete unit
and its section context, were read from the registered retained snapshot
`external-lean-reuse-snapshots-2026-10-21`; attribution is supplemented by
`nyll-classfieldtheory-fbd320cd-supplement`.

Worker 666 made these modifications:

- Extract M300.002 into the focused `AbsoluteBase/U002/Proofs` module and
  prefix its namespace with `Langlands.NYLL`.
- Write the source section variables `(K : Type) [Field K]` as leading
  theorem binders and give the theorem the published target applied to
  these same arguments as its type.
- Replace the broad source imports by the published statement module and
  `GaloisExtensionQuotient.Initial.U001.Proofs`, which supply the target,
  data and base equality. Retain the used openings `CyclicCohomology` and
  `ClassFormation` and drop the unused openings.
- Replace `mem_extensionSubgroup_iff` rewrites, the intermediate `hh'`,
  `hout` and `hout'`, and the final explicit coercion changes by
  definitional reduction of the published `extensionSubgroup` abbreviation.
  Keep the source construction of `h'` and `g'` and the application of
  `L.normal.conj_mem`.

The original copyright, author header and theorem docstring are retained.
The existing Apache-2.0 files
[`licenses/NYLL/LICENSE`](../../../../../../../../../licenses/NYLL/LICENSE)
and [`licenses/NYLL/NOTICE`](../../../../../../../../../licenses/NYLL/NOTICE)
remain unchanged.

## Development validation

In environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`, check
`e7a4ad0d-50cc-4edc-b77e-9d660bb65cd8` compiled the focused draft with no
errors or warnings. Check `9b519281-86ec-4ef2-a09e-e530cb1e5b1d` built the
workspace module with Lake and inspected the theorem with no errors or
warnings, no universe parameters, and only the standard assumptions
`propext`, `Classical.choice` and `Quot.sound`. These development checks
are separate from the candidate's exact-target validation, independent
semantic review and Library publication.

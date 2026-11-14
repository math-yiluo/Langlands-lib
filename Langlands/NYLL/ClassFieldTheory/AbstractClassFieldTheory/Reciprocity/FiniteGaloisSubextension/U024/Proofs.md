# NYLL M040.024: `finite_extension_trans`

## Exact target and implemented proof

For `{G : Type u}` with `[Group G]` and `[TopologicalSpace G]`,
`{P L K : ClosedSubgroup G}`, inclusions `hPL : P.toSubgroup ≤ L.toSubgroup`
and `hLK : L.toSubgroup ≤ K.toSubgroup`, and the source's two finite-coset
instances `hPLfinite` and `hLKfinite`, the theorem proves exactly
`finite_extension_transStatement hPL hLK`. Its conclusion is finiteness of
`K.toSubgroup ⧸ extensionSubgroup K P (hPL.trans hLK)`.
Normality is not a hypothesis: these quotients are coset types.

The proof retains source M040.024, lines 225–247. It obtains nonzero relative
indices for both finite coset types with `Subgroup.index_ne_zero_of_finite`,
combines them with `Subgroup.relIndex_ne_zero_trans`, and derives finiteness
of the endpoint coset type with `Nat.finite_of_card_ne_zero`.
`extensionSubgroup` is the subgroup restricted to the ambient subgroup, so
unfolding `Subgroup.relIndex` gives exactly the indices used.
All these lemmas are Mathlib results available through the existing statement
imports; no earlier theorem from this task is needed. The source proof body
is unchanged apart from expressing its conclusion by the published target.

The full theorem name is `Langlands.NYLL.ClassFormation.FiniteGaloisSubextension.finite_extension_trans`; its published target is `Langlands.NYLL.ClassFormation.FiniteGaloisSubextension.finite_extension_transStatement`.

## Source and modifications

Adapted from Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FiniteGaloisSubextension.lean`
(SHA-256 `c3b543d031492dac28deef22332941e7ff6bda845aa34e8be3ecd6c59d87098e`).
The readable pinned source is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
Its registered sources are `external-lean-reuse-snapshots-2026-10-21`
(content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and `nyll-classfieldtheory-fbd320cd-supplement`
(`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).

Worker 185 extracted this one theorem, prefixed the source namespace with
`Langlands.NYLL`, replaced the broad source import by the published focused
`FiniteGaloisSubextension.Statements` module, and wrote the theorem's type
as the corresponding published `Statement` applied to the original parameters.
The original copyright and author header is retained. See
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
The implementation changes specific to this theorem are described above.
No imported Lean or Markdown file is modified.

This is an abstract subgroup result. It supplies no host class-formation,
cup-product, transfer, Tate-cohomology or reciprocity theorem.

# NYLL M040.025: `finite_extension_over_intermediate`

## Exact target and implemented proof

For `{G : Type u}` with `[Group G]` and `[TopologicalSpace G]`,
`{P M K : ClosedSubgroup G}`, inclusions `hPK : P.toSubgroup ≤ K.toSubgroup`,
`hMK : M.toSubgroup ≤ K.toSubgroup`, and `hPM : P.toSubgroup ≤ M.toSubgroup`,
and the finite-coset instance `hPKfinite`, the theorem proves exactly
`finite_extension_over_intermediateStatement hPK hMK hPM`: finiteness of
`M.toSubgroup ⧸ extensionSubgroup M P hPM`. No normality is assumed.

The proof retains source M040.025, lines 248–272. Finiteness of the endpoint
coset type makes `P.toSubgroup.relIndex K.toSubgroup` nonzero.
If `P.toSubgroup.relIndex M.toSubgroup` vanished, the tower identity
`Subgroup.relIndex_mul_relIndex` would force that endpoint index to vanish.
The resulting nonzero intermediate index yields the claimed finiteness via
`Nat.finite_of_card_ne_zero`. The subgroup/index comparisons are definitional
after unfolding `Subgroup.relIndex`. The source proof body is unchanged apart
from its named target type. It uses only the published statement module,
the existing definitions and Mathlib; M040.024 is not a proof dependency.

The full theorem name is `Langlands.NYLL.ClassFormation.FiniteGaloisSubextension.finite_extension_over_intermediate`; its published target is `Langlands.NYLL.ClassFormation.FiniteGaloisSubextension.finite_extension_over_intermediateStatement`.

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

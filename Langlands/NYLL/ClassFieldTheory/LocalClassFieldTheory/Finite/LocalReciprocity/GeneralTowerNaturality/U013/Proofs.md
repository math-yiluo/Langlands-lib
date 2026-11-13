# Restriction along an algebra equivalence is conjugation: proof

`Langlands.NYLL.LocalClassFieldTheory.restrictNormalHom_eq_autCongr` proves the
published target
`Langlands.NYLL.LocalClassFieldTheory.restrictNormalHom_eq_autCongrStatement` for
every choice of its parameters:

```lean
theorem restrictNormalHom_eq_autCongr
    (K L M : Type)
    [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    [Normal K M]
    (e : L ≃ₐ[K] M) :
    restrictNormalHom_eq_autCongrStatement K L M e
```

So when `L` is made an `M`-algebra through `e.symm` (with the scalar tower
`K → M → L` built in the target), Mathlib's restriction
`AlgEquiv.restrictNormalHom M : Gal(L/K) →* Gal(M/K)` equals
`(AlgEquiv.autCongr e).toMonoidHom`, conjugation by `e`.
All three fields lie in `Type 0`, exactly as in the source. The binder order
and kinds above are the complete theorem telescope. No finite-dimensionality,
Galois, topology, valuation or local-field hypotheses are added.

## Proof

The proof is the source proof, unchanged.

1. It installs the same two local instances as the target, with the same proof
   term for the scalar tower, so the goal's `letI` bindings agree with them.
2. `MonoidHom.ext` and `AlgEquiv.ext` reduce the equation to
   `(restrictNormalHom M sigma) x = (autCongr e sigma) x` for `sigma : Gal(L/K)` and
   `x : M`. Since `e.symm` is injective, it suffices to compare the images under
   `e.symm`.
3. On the left, `e.symm` is `algebraMap M L` for the installed algebra
   structure, so `AlgEquiv.restrictNormal_commutes sigma M x` gives
   `sigma (e.symm x)`.
4. On the right, `simp [AlgEquiv.autCongr_apply]` rewrites
   `e.symm ((autCongr e sigma) x) = e.symm (e (sigma (e.symm x)))` to
   `sigma (e.symm x)`.

## Source and modifications

Source: Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/GeneralTowerNaturality.lean`
(SHA-256 `a81fa466df15d0d72f24428f0780a68b9a9f434fa4d27746beafe71bfae521c0`),
theorem `LocalClassFieldTheory.restrictNormalHom_eq_autCongr` at lines 402–436
(inventory M262.013). The retained original is in the project literature folder
`External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`,
registered as `external-lean-reuse-snapshots-2026-10-21` (fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`); the attribution
supplement is `nyll-classfieldtheory-fbd320cd-supplement` (fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalClassFieldTheory.restrictNormalHom_eq_autCongr` (M262.013) | `Langlands.NYLL.LocalClassFieldTheory.restrictNormalHom_eq_autCongr` |

Modifications: the namespace gains the `Langlands.NYLL` prefix; the conclusion is
written as the published target applied to the telescope instead of the
`letI`-bound equation it unfolds to; the only import is the statement module.
The telescope, docstring and tactic proof are unchanged. The source's
`noncomputable section` is retained. Every other source declaration and its
module-level discussion are omitted from this focused proof file, and a new
module docstring identifies this unit. The original attribution header is
retained, followed by dated adaptation and verification records.

## Imports and scope

The only direct import is
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GeneralTowerNaturality.U013.Statements`.
That published target directly imports `Mathlib.FieldTheory.Normal.Defs`.
This supplies `AlgEquiv.restrictNormalHom` and
`AlgEquiv.restrictNormal_commutes`; its transitive Mathlib imports supply
`AlgEquiv.autCongr`, `AlgEquiv.autCongr_apply`, the two extensionality lemmas and
the scalar-tower construction. There is no additional helper module or NYLL
mathematical dependency.

The original module directly imports `Mathlib.GroupTheory.Abelianization.Defs`,
`Nyll.ClassFieldTheory.AlgebraicNumberTheory.SeparableClosureEmbedding`,
`Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData`
and
`Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.NormResidueNaturality`.
All four imports are replaced by the published statement import above. The
implemented proof uses only the Mathlib results available through that target.
The target's Lean/Markdown pair and its imports are unchanged.

This proves the named equality of restriction and conjugation homomorphisms.
It does not assert a reciprocity theorem or a comparison with the host
class-field-theory constructions. The later source unit M262.014 is a separate
consumer of this theorem.

The module compiled with zero errors and zero warnings in approved environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`). This development check is not
independent acceptance. Worker 295 repeated the build and theorem inspection
with diagnostic `1d177342-ac38-494d-a3e5-ac286160f73b`; it reports no universe
parameters and only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`. Worker 89 supplied the complete proof draft; Worker 295
compared it with the pinned original and prepared this documented submission
without changing the tactic proof.

## License

The Lean file keeps the original copyright and author header unchanged:
Copyright (c) 2026 Naganori Yamaguchi; Authors: Naganori Yamaguchi (assisted by
OpenAI Codex). It remains under Apache-2.0. The already-published `licenses/NYLL/LICENSE`
and `licenses/NYLL/NOTICE` are reused unchanged and included through
`repository_paths`. Their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
Worker 89 adapted the proof directly from the pinned original; Worker 295
retained that draft and expanded the documentation.

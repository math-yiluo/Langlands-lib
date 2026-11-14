# Finite Galois realization: the quotient equivalence on representatives

This module defines one closed proposition in
`Langlands.NYLL.LocalClassFieldTheory`, the statement phase of source row
M098.027:

- `finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding_mk_applyStatement`,
  for the source theorem
  `finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding_mk_apply`.

It is a `def` returning `Prop` that packages the complete source theorem
signature. It is not proved here. A later proof child will prove it under
the name
`Langlands.NYLL.LocalClassFieldTheory.finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding_mk_apply`.

## The proposition

It universally quantifies, in the source order,

```lean
(K L : Type) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  (i : L →ₐ[K] SeparableClosure K)
  (τ : (intrinsicAbstractBase K).toSubgroup) (x : L)
```

and concludes

```lean
i ((finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L i
  (QuotientGroup.mk τ)) x) = τ.1 (i x)
```

So `L / K` is a finite Galois extension of fields in `Type` (universe zero,
as in the source), and `i` is a `K`-embedding of `L` into Mathlib's
separable closure `SeparableClosure K`. There is no valuation, topology or
local-field hypothesis.

- In the source the first seven binders are the section variables of the
  file (source lines 33–34). The theorem has no `omit`, so, by Lean's rule
  for theorem statements, all of them are binders of the source theorem,
  including `[FiniteDimensional K L]` and `[IsGalois K L]`. The proposition
  quantifies over them in the same order.
- `intrinsicAbstractBase K` (source row M091.003) is the closed subgroup of
  `Gal(SeparableClosure K / K)` fixing the bottom intermediate field, which is
  the whole group. The source writes its type as `(B K).toSubgroup` with the
  file's private abbreviation `B K := intrinsicAbstractBase K` (source lines
  42–43). The port writes the unfolded term; the two are the same term after
  unfolding the reducible abbreviation.
- `finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L i` (source
  row M090.009) is the published equivalence between the quotient of
  `(closedFixingSubgroup K (SeparableClosure K) ⊥).toSubgroup` by the
  extension subgroup of the closed subgroup fixing `i(L)`, and `Gal(L / K)`.
  `QuotientGroup.mk τ` is the class of `τ` in that quotient.
- `τ.1` is the underlying element of `Gal(SeparableClosure K / K)`, applied
  to `i x`.

So the automorphism of `L` attached to the class of `τ` acts on `L`, after
applying `i`, as `τ` acts on `i(L)`.

## Reused Library declarations

| Source unit and original declaration | Library declaration used |
| --- | --- |
| M090.009, `LocalClassFieldTheory.finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding` | `Langlands.NYLL.LocalClassFieldTheory.finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding` (module `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteGaloisRealization.Quotient.Definitions`, imported) |
| M091.003, `LocalClassFieldTheory.intrinsicAbstractBase` | `Langlands.NYLL.LocalClassFieldTheory.intrinsicAbstractBase` (module `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData.Initial.Definitions`, imported) |

Both declarations are published in the Library and are used under these
names inside the namespace `Langlands.NYLL.LocalClassFieldTheory`, without
any `open` line. The
statement is otherwise the source text.

A development check compiled a proof of the proposition with no errors or
warnings, using only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`. It follows the source proof, with the private source helper
`baseFixingExtensionQuotientEquivGaloisGroup_mk_apply` (source row M098.026)
stated and proved as a local `have`. This only confirms that the statement is
formed as in the source; the proof belongs to the later proof child.

## Relation to other Library and Mathlib declarations

A search of the Library `.lean` files found no declaration that states this
proposition or another value formula for
`finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding`. The related
declarations are:

- `Langlands.NYLL.LocalClassFieldTheory.relativeCosetAction_intermediateFieldUnit_valStatement`
  (`...LocalReciprocity.SeparableUnitsNorm.BaseUnits.Statements`) evaluates
  `baseFixingExtensionQuotientEquivGaloisGroup` (source row M089.011, from
  which M090.009 is built), but in a statement about a coset action on units,
  not on a representative `τ`;
- `Langlands.NYLL.LocalClassFieldTheory.abstractSubgroupEquivGaloisGroup_applyStatement`
  (`...LocalReciprocity.FiniteAbstractFixedField.Initial.Statements`) has the
  same shape, `abstractSubgroupEquivGaloisGroup k Ω H σ x = σ.1 x`, for a
  different equivalence: the one between a closed subgroup `H` of
  `Gal(Ω / k)` and the Galois group of `Ω` over the fixed field of `H`;
- Mathlib's `InfiniteGalois.normalAutEquivQuotient_apply` and
  `AlgEquiv.restrictNormalHom_apply` compute the Mathlib maps that M089.011
  is built from. Neither states this proposition.

## Original source

The original source is Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ConcreteReciprocityCanonical.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ConcreteReciprocityCanonical.lean>).
The complete file was read and its SHA-256 verified as
`1d616a601ddd3a0a8f52c11f29d77cb1a30f9946335fa4ecef070f3a32385ad6`.
The M098.027 docstring occupies lines 623–624, the `@[simp]` attribute line
625 and the signature lines 626–629; its proof occupies lines 630–644. The
header occupies lines 1–5, the namespace line 22, the `open` lines 23–27,
the `noncomputable section` line 31, the section variables lines 33–34 and
the private abbreviation `B` lines 42–43. The theorem lies inside
`section EmbeddingConjugation` (lines 338–1069), which declares no further
variables.

| Source unit and original declaration | Adapted declaration and phase |
| --- | --- |
| M098.027, `LocalClassFieldTheory.finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding_mk_apply` | `Langlands.NYLL.LocalClassFieldTheory.finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding_mk_applyStatement`, closed Prop target |
| Same source theorem, later proof phase | `Langlands.NYLL.LocalClassFieldTheory.finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding_mk_apply`, reserved for the proof child |

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
with supplement `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Modifications and attribution

Worker 57 made these changes to the source theorem:

- The theorem becomes a Prop-valued definition with the `Statement` suffix.
  The section variables it uses and its explicit parameters become universal
  binders in the same order, and the proof is omitted for the separate proof
  phase.
- The private abbreviation `B K` is unfolded to `intrinsicAbstractBase K`.
  The conclusion is otherwise the source text.
- The `@[simp]` attribute is omitted, since the definition is a proposition,
  not a rewrite rule. The proof child may restore it on the theorem.
- The namespace `LocalClassFieldTheory` is prefixed with `Langlands.NYLL`.
- The source imports are replaced by the two Library modules in the table
  above.
- The `noncomputable section` and the three `open` lines are omitted; the
  statement uses no name from the opened namespaces. All other declarations
  of the source file are omitted.

The Lean header keeps the original 2026 Naganori Yamaguchi copyright,
the authorship line including OpenAI Codex assistance, and the Apache-2.0
notice. It also records these modifications. The existing
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) match the pinned
upstream files. Their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

This unit contains only the M098.027 statement target. Its proof and the
other rows of the source file are not part of this unit.

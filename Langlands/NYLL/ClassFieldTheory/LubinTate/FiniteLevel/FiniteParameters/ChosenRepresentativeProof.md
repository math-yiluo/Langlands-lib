# NYLL M358.006: `standardLubinTateUnitParameterChosenRepresentative_spec`

Worker 439, 14 November 2026. This module proves the published proposition
`Langlands.NYLL.LubinTate.standardLubinTateUnitParameterChosenRepresentative_specStatement`
with the theorem
`Langlands.NYLL.LubinTate.standardLubinTateUnitParameterChosenRepresentative_spec`.

## Target

For implicit `{K : Type u} [Field K]`, explicit `F : LocalField.{u,v} K`,
`n : ℕ` and `a : standardLubinTateUnitParameter F n`, the theorem's
conclusion is the published target applied to exactly these arguments,
`standardLubinTateUnitParameterChosenRepresentative_specStatement F n a`.
Unfolded, it says that the quotient class of the chosen valuation-ring unit
`standardLubinTateUnitParameterChosenRepresentative F n a` in
`F.valuationSubringˣ ⧸ U^(n+1)` is `a` itself:

`standardLubinTateUnitParameterClass F n
  (standardLubinTateUnitParameterChosenRepresentative F n a) = a`.

Here `U^(n+1)` is
`CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF (n + 1)`, and the
quotient type, class map and chosen representative are the published
definitions in
`Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.FiniteParameters.Definitions`.
The two universes `u` and `v` stay independent, and every parameter keeps
its source explicitness. The theorem adds no hypothesis, and the module
declares no instance, axiom or other declaration. As in the source, the
theorem carries `@[simp]`.
Because its type is the Prop-valued target definition rather than a visible
equation, simp registers it as a rewrite of that proposition to `True`.
A private development check confirmed that `simp` proves the applied target
`standardLubinTateUnitParameterChosenRepresentative_specStatement F n a`, but
makes no progress on the spelled-out equation. So, unlike the source lemma,
this simp lemma does not rewrite the class of the chosen representative to
`a`. That form would need a separate equation lemma, which this task does not
include.

## Implemented proof

The proof is a single term. The published representative is defined as
`Classical.choose h`, where `h` is
`QuotientGroup.mk'_surjective (CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF (n + 1)) a`.
This is the surjectivity of the canonical quotient homomorphism, applied to
`a`, so `h` is a proof of `∃ x, QuotientGroup.mk' U^(n+1) x = a`.
`Classical.choose_spec h` proves the property of the chosen witness,
`QuotientGroup.mk' U^(n+1) (Classical.choose h) = a`.
The published class map `standardLubinTateUnitParameterClass F n` is by
definition `QuotientGroup.mk' U^(n+1)`. So Lean accepts this term as a
proof of the target by unfolding the target, the class map and the
representative definitionally. No tactic, rewriting or extra lemma is needed.
The axioms used are `propext`, `Classical.choice` and `Quot.sound`.

## Imports

The only import is the published target module
`Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.FiniteParameters.RepresentativeStatements`.
It imports the Definitions module, which provides `QuotientGroup.mk'` and
`QuotientGroup.mk'_surjective` through `Mathlib.GroupTheory.QuotientGroup.Defs`.
The target's Lean/Markdown pair and all its imports are unchanged.

## Source correspondence, attribution and modifications

The source is Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LubinTate/FiniteLevel/FiniteParameters.lean`:
the `@[simp]` attribute is on line 87, the type on lines 88–92 and the proof
on lines 93–95. The readable retained copy is
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LubinTate/FiniteLevel/FiniteParameters.lean`.
Its file SHA-256 is
`c1254bd8cbffb7941e723d32b6a47ccc353bb2265211c86c99565dc47c2cd92d`.
Registered sources: `external-lean-reuse-snapshots-2026-10-21`, content
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`; and
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The proof term is the source's term unchanged.

Copyright 2026 Naganori Yamaguchi; original author Naganori Yamaguchi
(assisted by OpenAI Codex). The source header is kept, followed by a
modification record. Changes: only this one theorem is extracted; its
namespace is prefixed with `Langlands.NYLL`; its conclusion is written as the
published target proposition applied to its arguments rather than the
spelled-out equation; and the upstream imports are replaced by the single
published target import. The theorem name, `@[simp]` attribute, universes,
binders and proof term are unchanged. The Apache-2.0 license and notices
are kept unchanged in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`,
SHA-256 respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
Worker 298 extracted the target statement and recorded this proof term in
an unreviewed LTa draft. That draft was used only as development evidence.

The development environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096`
(Lean 4.34.0; Mathlib `5ed2965256430c3649e86755f9576b54eca72435`).
Development compilation is not independent acceptance; publication requires
independent review, the Lake build and the exact-target check.

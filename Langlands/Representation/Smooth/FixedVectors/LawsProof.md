# Algebraic laws of subgroup-fixed vector restriction

`Langlands.fixedVectorsLaws` proves the complete proposition in
[LawsStatement.md](LawsStatement.md). All component lemmas remain in this
same proof module.

The coefficient ring `R`, acting group `G`, and modules `V`, `W`, and `U`
have five independent carrier universes. The only ambient instances are
`CommRing R`, `Group G`, and `AddCommGroup` and `Module R` for each of the
three module carriers. The representations, intertwiners, equivalences and
arbitrary subgroups are quantified inside the accepted clauses.
The third module occurs in the composition clause. Injectivity of the
original intertwiner is the premise of the sixth map clause, not an
additional assumption on the closing theorem. No topology, smoothness,
finite generation, Noetherianity, normality, or admissibility is assumed.

The component lemmas correspond to the target in its original order:

| Clause | Component lemma |
| --- | --- |
| Map carries fixed vectors to fixed vectors | `map_mem_fixedVectors` |
| Map evaluation in the ambient module | `fixedVectorsMap_apply` |
| Compatibility with subtype inclusions | `subtype_comp_fixedVectorsMap` |
| Restriction of the identity | `fixedVectorsMap_id` |
| Restriction of a composite | `fixedVectorsMap_comp` |
| Injectivity of the restricted map when the original map is injective | `fixedVectorsMap_injective` |
| Equivalence evaluation | `fixedVectorsEquiv_apply` |
| Inverse equivalence evaluation | `fixedVectorsEquiv_symm_apply` |
| Underlying linear map of the restricted equivalence | `fixedVectorsEquiv_toLinearMap` |
| Compatibility with the inverse equivalence | `fixedVectorsEquiv_symm` |

`map_mem_fixedVectors` uses the codomain-membership field of `fixedVectorsMap`.
The evaluation and subtype-inclusion formulas reduce to the original
intertwiner. Identity and composition follow by linear-map extensionality
and reduction. For injectivity, equality of restricted images gives equality
of the original images under subtype coercion; injectivity of the original
intertwiner followed by subtype extensionality gives equality of the inputs.
`fixedVectorsMapLaws` introduces all six clauses' quantifiers and assembles
these lemmas.

The forward and inverse evaluation formulas for `fixedVectorsEquiv`, and its
underlying-linear-map formula, follow by reduction. Compatibility with the
inverse equivalence follows by extensionality and reduction of the inverse
function. `fixedVectorsEquivalenceLaws` introduces its representation,
equivalence, and subgroup quantifiers and assembles these four identities.
`fixedVectorsLaws` pairs the two results without additional hypotheses.

This is Worker 0's internal algebraic proof. The exact accepted definitions,
source provenance, and ambient assumptions are recorded in the adjacent
statement Markdown. The target is accepted statement
`d720bdcb-b2b8-4bf6-9b86-31702bea43e6`, version 1, published at
`61f9628d1033c8302398370f5bd2922af38dcac6`, with independent receipt
`446948a4-f644-46f3-a7f2-d6437d5a8a81`. Its complete proposition fingerprint is
`5c8767aaa1fb2f29235a2b5c6eefd552430f665e0c9eeaec7d928db57a242fcd`.
The sole import is this target. Its transitive project definitions are
`7ad85b8b-caae-4345-ac1b-2c2d551dbb94` and
`665022df-625b-44ae-9dbd-425f6e266bab`, both version 1.
All six effective source files were checked against the exact accepted
integrated records, and all three artifacts were confirmed published and
current before submission.

The environment is `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1,
Lean 4.34.0 at `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b` and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
The relevant Mathlib identity and composition definitions are in
`RepresentationTheory/Intertwining.lean`, lines 199-223; its representation
equivalence, underlying-map and inverse definitions are at lines 312-321 and
384-400 of that pinned version.

Worker 0 authored the complete Lean proof and original explanation.
Worker 12 reused the Lean file unchanged, checked the exact target and
dependency closure, and expanded the scope and clause mapping here.
Native compilation of the dependency closure and proof succeeded.
Scope inspection confirmed the complete five-universe closing theorem and
its original algebraic hypotheses. The two clause theorems and the closing
theorem have axiom closures containing only `propext` and `Quot.sound`.
These are development checks.
Independent acceptance requires the registered proof checker, semantic
review, and Library publication. This is an algebraic infrastructure result;
it makes no claim to complete the local Langlands correspondence.

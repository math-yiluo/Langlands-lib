# NYLL M267.003: canonical comparison proof

`Langlands.NYLL.LocalClassFieldTheory.normQuotientToUnramifiedNormQuotient_mk` proves exactly
`Langlands.NYLL.LocalClassFieldTheory.normQuotientToUnramifiedNormQuotient_mkStatement`.
The comparison map sends a norm class to the corresponding unramified valuation class.

## Implemented proof

The proof introduces the two Type-zero fields, all fifteen original instance
arguments and the unit `x`, then closes the equation by `rfl`. The canonical
comparison is defined using `normQuotientLift`, which is implemented by
`QuotientGroup.lift`. Evaluating it on `normClass K L x` reduces definitionally
to `unramifiedNormClass K (Module.finrank K L) x`. The proof therefore uses
reflexivity with no auxiliary lemma. The original `simp` attribute is retained.

The target quantifies over K L : Type and the original fifteen instance
arguments: the two fields, their valuation relations, topologies and local-field
certificates, the algebra structure, finite dimensionality, Galoisness, valuation
extension, integral closure and finite integer-ring module, and the published
unramifiedness class. These are the hypotheses of the imported closed target;
none is added or removed. The proof declares no additional instances.
The map and quotient objects are reused by their adapted Lean names.

## Source and modifications

Original source: `LocalClassFieldTheory.normQuotientToUnramifiedNormQuotient_mk`, lines 73–79,
with shared telescope lines 34–44 of
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/UnramifiedNormComparison.lean`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`.
The pinned whole-file SHA-256 is
`a955313b05e5cdeb8bd4e9c6c76e466c956fe7231bb6fd90f4945a57e564ad26`.
The readable copy belongs to `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/`; the attribution supplement
is `nyll-classfieldtheory-fbd320cd-supplement`.

Worker 205 adapted this proof on 16 November 2026 by prefixing the namespace,
importing the focused target and required published dependencies, introducing
its closed telescope and omitting unrelated declarations and the redundant
noncomputable section. The source `rfl` proof and `simp` attribute are retained.
The original docstring, copyright and author header remain, with this dated
modification record and focused documentation added. Original license and
notices remain at `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.

Worker 562 reused Worker 205's proof-only shared draft (revision 1 for
Task 7269) on 16 November 2026, verified the original file fingerprint and
published target, and clarified the explanation of definitional reduction.
Only this proof pair is submitted; the published target and all its imported
data remain unchanged. Independent semantic review and exact-target
validation are required for publication.

# Surjectivity of the base-to-ambient quotient map

`Langlands.NYLL.LocalClassFieldTheory.baseFixingToAmbientQuotient_surjective`
proves exactly
`Langlands.NYLL.LocalClassFieldTheory.baseFixingToAmbientQuotient_surjectiveStatement K Ω E`
for fields `K Ω : Type 0`, an algebra `K → Ω`, `[IsGalois K Ω]`, an
intermediate field `E` and `[IsGalois K E]`. The map from the bottom-field
fixing subgroup onto the ambient Galois quotient by the subgroup fixing `E`
is surjective.

The implemented proof is the source proof. Quotient induction reduces a class
to a representative `σ : Gal(Ω/K)`. Mathlib's
`IntermediateField.fixingSubgroup_bot` and `Subgroup.mem_top` put `σ` in the
bottom-field fixing subgroup. Its subtype is the desired preimage, and its
image is the original class by definition of the published
`baseFixingToAmbientQuotient`. Inputs are the published target and its imports,
including that map and `closedFixingSubgroup`, together with Mathlib quotient
induction. Neither of the earlier M089 proof modules is needed.

Adapted by Worker 213 from Naganori Yamaguchi's ClassFieldTheory, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/GaloisExtensionQuotient.lean`,
lines 101–115 (M089.008). Registered source:
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The retained source root is
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.

Modification record: extract this theorem into the required focused module;
prefix its namespace with `Langlands.NYLL`; replace broad source imports by the
published target module; express the conclusion with the exact named Prop target;
retain all source binders and the proof body; omit unused namespace openings.
The original copyright and author header is retained. Apache-2.0 license and
notices remain in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
This support proof does not discharge a host reciprocity or cohomology target.

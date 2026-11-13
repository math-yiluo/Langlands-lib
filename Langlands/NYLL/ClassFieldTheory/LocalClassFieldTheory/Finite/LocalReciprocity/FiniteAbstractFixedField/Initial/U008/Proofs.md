# Evaluation of the abstract subgroup Galois equivalence

`Langlands.NYLL.LocalClassFieldTheory.abstractSubgroupEquivGaloisGroup_apply`
proves exactly
`Langlands.NYLL.LocalClassFieldTheory.abstractSubgroupEquivGaloisGroup_applyStatement k Ω H σ x`.
Here `k Ω : Type 0` are fields with an algebra and `[IsGalois k Ω]`,
`H` is a closed subgroup of `Gal(Ω/k)`, `σ : H.toSubgroup`, and `x : Ω`.
The canonical equivalence from `H.toSubgroup` to
`Gal(Ω/abstractFixedField k Ω H)` sends `σ` to an automorphism whose value
at `x` is `σ.1 x`.

The implemented proof is the source term `rfl`. The published
`abstractSubgroupEquivGaloisGroup` is the composite of subgroup congruence and
`IntermediateField.fixingSubgroupEquiv`; both retain the same underlying
automorphism, so the asserted evaluation equality is definitional. The only
NYLL inputs are the published target and its imports, including the actual
equivalence definition. There is no finiteness or openness assumption.

Adapted by Worker 213 from Naganori Yamaguchi's ClassFieldTheory, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteAbstractFixedField.lean`,
lines 109–114 (M099.008), with the source telescope at line 31 and equivalence
at lines 100–107. Registered source:
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The retained source root is
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.

Modification record: extract this theorem into the required focused module;
prefix its namespace with `Langlands.NYLL`; replace broad source imports by the
published target module; state the conclusion using the exact named Prop target;
retain the original binders, proof term and `simp` attribute; omit unused
namespace openings. The original copyright and author header is retained.
Apache-2.0 license and notices remain in `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`. This support proof does not discharge a host reciprocity
or cohomology target.

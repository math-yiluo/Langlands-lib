# Subgroup inclusion reverses inclusion of abstract fixed fields

`Langlands.NYLL.LocalClassFieldTheory.abstractFixedField_le` proves exactly
`Langlands.NYLL.LocalClassFieldTheory.abstractFixedField_leStatement k Ω hLK`.
Here `k Ω : Type 0` are fields with an algebra, `K L` are implicit closed
subgroups of `Gal(Ω/k)`, and the explicit hypothesis is
`hLK : L.toSubgroup ≤ K.toSubgroup`. The conclusion is
`abstractFixedField k Ω K ≤ abstractFixedField k Ω L`. There is no Galois,
finiteness or openness hypothesis.

The implemented proof is the source term
`IntermediateField.fixedField_le hLK`. The published `abstractFixedField`
abbreviation is the actual intermediate field fixed by the underlying subgroup,
so Mathlib's reversal of subgroup inclusion has exactly the required type.
The only NYLL inputs are the published target and its imports. The proof does not
depend on the separate fixed-field recovery theorem.

Adapted by Worker 213 from Naganori Yamaguchi's ClassFieldTheory, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteAbstractFixedField.lean`,
lines 92–98 (M099.006), with the source section telescope at line 31. Registered
source: `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The retained source root is
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.

Modification record: extract this theorem into the required focused module;
prefix its namespace with `Langlands.NYLL`; replace broad source imports by the
published target module; state the conclusion using the exact named Prop target;
retain the original binders, `omit [IsGalois k Ω]`, and proof term; omit unused
namespace openings. The original copyright and author header is retained.
Apache-2.0 license and notices remain in `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`. This support proof does not discharge a host reciprocity
or cohomology target.

# Projection of the fixed-field unit equivalence

`Langlands.NYLL.LocalClassFieldTheory.abstractFixedFieldUnitsEquivGaloisFixed_coe`
proves exactly
`Langlands.NYLL.LocalClassFieldTheory.abstractFixedFieldUnitsEquivGaloisFixed_coeStatement k Ω H x`.
Here `k Ω : Type 0` are fields with an algebra, `H` is a closed subgroup of
`Gal(Ω/k)`, and `x : Additive (abstractFixedField k Ω H)ˣ`.
Projecting `abstractFixedFieldUnitsEquivGaloisFixed k Ω H x` to
`Additive Ωˣ` gives
`intermediateFieldUnitsToGaloisAmbient k Ω (abstractFixedField k Ω H) x`.
There is no Galois, finiteness or openness hypothesis.

The implemented proof is the source term `rfl`. The forward map of the
published `abstractFixedFieldUnitsEquivGaloisFixed` constructs a subtype whose
value is exactly the displayed ambient unit inclusion. Projection removes its
fixedness proof, giving the required definitional equality. The only NYLL
inputs are the published target and its imports, including the actual
fixed-field unit equivalence and ambient inclusion definitions.

Adapted by Worker 213 from Naganori Yamaguchi's ClassFieldTheory, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/AbstractFixedFieldUnits.lean`,
lines 81–91 (M101.002), with the equivalence at lines 38–79. Registered source:
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The retained source root is
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.

Modification record: extract this theorem into the required focused module;
prefix its namespace with `Langlands.NYLL`; replace broad source imports by the
published target module; state the conclusion using the exact named Prop target;
retain the original binders, `omit [IsGalois k Ω]`, proof term and `simp`
attribute; omit unused namespace openings. The original copyright and author
header is retained. Apache-2.0 license and notices remain in
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`. This support proof does not
discharge a host reciprocity or cohomology target.

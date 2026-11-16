# Quotient representatives and the concrete relative Galois action

`Langlands.NYLL.LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup_mk_apply_val`
proves exactly the published
`abstractExtensionQuotientEquivGaloisGroup_mk_apply_valStatement k Ω K L hLK hnormal σ x`.
For Type-0 fields `k`, `Ω` with `Algebra k Ω` and `IsGalois k Ω`, closed
subgroups `L ≤ K`, normality of `L` in `K`, `σ ∈ K`, and `x` in the
relative fixed field, the actual quotient/Galois equivalence sends the
coset of `σ` to an automorphism whose value at `x`, viewed in `Ω`, is
`σ.1 (x : Ω)`. All source hypotheses and the target's local normality
instance are retained.

## Implemented proof

Expose the target equality with `change`. Install the given normality and
the published `abstractRelativeFixingSubgroup_normal` (M099.011) locally,
both for the actual fixing subgroup and its closed-subgroup presentation
`H`. The ambient quotient equivalence sends a representative to the coset
of `abstractSubgroupEquivGaloisGroup k Ω K σ`; this is a definitional `rfl`
calculation. Unfold `abstractExtensionQuotientEquivGaloisGroup` and its
compositions, using that calculation. Mathlib's
`InfiniteGalois.normalAutEquivQuotient_apply`, `AlgEquiv.autCongr_apply`,
and the `IntermediateField.equivOfEq` evaluation rules reduce the result
to restriction of the ambient automorphism. Finally,
`AlgEquiv.restrictNormalHom_apply` and `rfl` give the equality in `Ω`.

The focused statement import supplies the published quotient equivalences,
relative fixed-field constructions and normality proof transitively; the
proof introduces no new public definitions, instances or prerequisite lemmas.
The statement and its imported files remain unchanged.

## Source and modifications

Adapted by Worker 213 from Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory*, commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/AbstractFixedFieldUnits.lean`,
M101.007, signature lines 151–162 and proof lines 163–202. The original file
has SHA-256 `9a2d82d81f9f00269a7f9904e005ab931bbde64ea62cbe8fe7327d7b31a017f1`
and is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.
Registered sources: `external-lean-reuse-snapshots-2026-10-21`
(fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).

The source proof is preserved with a leading `change` exposing the published
Prop definition. The port isolates this theorem, prefixes its namespace with
`Langlands.NYLL`, replaces source imports by the published statement module,
uses the exact `Statement` application as its result type, and omits unused
namespace openings and unrelated source declarations. The source abbreviation
`extensionSubgroup` is definitionally the Mathlib subgroup in the target.
This proves only the specified NYLL support result.

The original copyright, authorship and Apache-2.0 header are retained.
The original license and notices remain in `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.

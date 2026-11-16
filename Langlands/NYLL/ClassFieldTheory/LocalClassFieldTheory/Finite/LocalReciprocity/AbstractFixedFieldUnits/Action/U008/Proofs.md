# Relative coset action on concrete fixed-field units

`Langlands.NYLL.LocalClassFieldTheory.relativeCosetAction_abstractRelativeFixedFieldUnit_val`
proves exactly the published
`relativeCosetAction_abstractRelativeFixedFieldUnit_valStatement k Ω K L hLK hnormal x q`.
For Type-0 fields `k`, `Ω` with `Algebra k Ω` and `IsGalois k Ω`, closed
subgroups `L ≤ K`, normality of the relative subgroup, an additive-tagged
unit `x` in the relative fixed field and a relative coset `q`, the actual
abstract coset action and the concrete relative Galois action have the same
underlying value in `Ω`. Both actions use the constructed unit comparison
and quotient/Galois equivalence in the unchanged target.

## Implemented proof

The private `quotientRepresentative_apply_val_local` proves the M101.007
representative-evaluation proposition, using its source proof. After exposing
the target equality, it installs normality for the actual fixing subgroup
and its closed-subgroup presentation. The ambient quotient map on a
representative is computed by `rfl`. Unfolding the composed quotient/Galois
equivalence and applying `InfiniteGalois.normalAutEquivQuotient_apply`,
`AlgEquiv.autCongr_apply`, the `IntermediateField.equivOfEq` evaluation
rules and `AlgEquiv.restrictNormalHom_apply` reduces its value to the
original ambient automorphism. The published statement import supplies the
fixed-field constructions and `abstractRelativeFixingSubgroup_normal`
(M099.011) used in this step.

For M101.008, unfold its proposition definition, install the supplied
normality locally and induct on the quotient `q`. For a representative
`σ`, the published `ClassFormation.relativeCosetAction_mk` (M024.002)
rewrites the relative coset action as the ambient action of `σ`. The
definitions of the unit comparison and the action on units reduce the
remaining equality to evaluation of `σ` on the underlying relative-field
unit. The private representative-evaluation lemma gives precisely that
equality. No finite-dimensionality or finite-index premise is added.

M101.007 is not imported from an unpublished candidate: its private source
proof is included under a distinct name, as the task permits. This pair
adds only the required public M101.008 theorem. The published target and
its imported files remain unchanged.

## Source and modifications

Adapted by Worker 213 from Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory*, commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/AbstractFixedFieldUnits.lean`.
M101.007 has signature lines 151–162 and proof lines 163–202; M101.008
has signature lines 206–224 and proof lines 225–233. The whole original
file has SHA-256 `9a2d82d81f9f00269a7f9904e005ab931bbde64ea62cbe8fe7327d7b31a017f1`
and is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.
Registered sources: `external-lean-reuse-snapshots-2026-10-21`
(fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).

The port prefixes the source namespace with `Langlands.NYLL`, replaces
broad source imports with the focused published statement and coset-action
proof modules, and omits unrelated declarations and unused namespace
openings. The public theorem and private prerequisite have the exact
published `Statement` applications as their result types. A leading
`change` in M101.007 and `unfold` in M101.008 expose these proposition
definitions. The private prerequisite is renamed, and the public proof
uses that name. The source proof bodies are otherwise retained. The source
abbreviation `extensionSubgroup` is definitionally the target's Mathlib
subgroup. This proves only the specified NYLL support result.

The original copyright, authorship and Apache-2.0 header are retained.
The original license and notices remain in `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.

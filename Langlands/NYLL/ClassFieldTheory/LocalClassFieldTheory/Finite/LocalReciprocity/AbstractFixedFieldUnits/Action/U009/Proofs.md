# Equivariance of the concrete fixed-field unit comparison

`Langlands.NYLL.LocalClassFieldTheory.abstractExtensionFixedRepresentationUnitsEquiv_action`
proves exactly the published
`abstractExtensionFixedRepresentationUnitsEquiv_actionStatement k Ω K L hLK hnormal q x`.
For Type-0 fields `k`, `Ω` with `Algebra k Ω` and `IsGalois k Ω`, closed
subgroups `L ≤ K`, normality of the relative subgroup, a relative coset
`q` and a vector `x` of the descended fixed representation, the constructed
additive carrier equivalence intertwines the descended quotient action
with the actual relative Galois action on upper fixed-field units. The
latter action is reindexed through the constructed quotient/Galois
equivalence. All the target's parameters and its local normality instance
are retained.

## Implemented proof

Two private source prerequisites establish the needed equality of ambient
values. `quotientRepresentative_apply_val_local` is M101.007: install the
normality of the fixing subgroup, compute the ambient quotient map on a
representative by `rfl`, and unfold the composed quotient/Galois
equivalence. Mathlib's normal quotient evaluation, automorphism conjugacy,
equality transport and restriction rules identify its value with the
original ambient automorphism. The published statement import supplies
the fixed-field constructions and M099.011 normality proof used here.
`cosetAction_unit_val_local` is M101.008: after unfolding its proposition
and installing normality, quotient induction reduces to a representative;
the published `ClassFormation.relativeCosetAction_mk` (M024.002) and the
private M101.007 proof compare the two actions on a fixed-field unit.

For M101.009, unfold its proposition and install normality locally. Apply
injectivity of `abstractRelativeFixedFieldUnitsEquivGaloisFixed` to the
desired equality. The published
`abstractRelativeUnitsEquiv_extensionUnitsEquiv` (M101.006) identifies the
composite carrier comparison on the left with the descended
representation's fixed coefficient. Extensionality for the fixed subtype,
the additive type tag and units reduces equality to their underlying
values in `Ω`. The published
`ClassFormation.extensionFixedRepresentation_action_coe` (M073.004)
identifies the descended action with `relativeCosetAction`. Rewrite the
fixed coefficient back using M101.006. The private M101.008 equality at
the image of `x` then proves the result.

The task permits private prerequisite proofs under distinct names while
the corresponding public results are unpublished. This pair imports no
unpublished proof module and adds only the required public M101.009
theorem. It assumes no carrier comparison or action law beyond the
published constructions and proved dependencies above. The target and
its imported files remain unchanged.

## Source and modifications

Adapted by Worker 213 from Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory*, commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/AbstractFixedFieldUnits.lean`.
M101.007 has signature lines 151–162 and proof lines 163–202; M101.008
has signature lines 206–224 and proof lines 225–233; M101.009 has
signature lines 237–253 and proof lines 254–274. The whole original file
has SHA-256 `9a2d82d81f9f00269a7f9904e005ab931bbde64ea62cbe8fe7327d7b31a017f1`
and is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.
Registered sources: `external-lean-reuse-snapshots-2026-10-21`
(fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).

The port prefixes the namespace with `Langlands.NYLL`, replaces broad
source imports with focused published modules, and omits unrelated
declarations and unused namespace openings. The public theorem and
private prerequisites have the exact published `Statement` applications
as their result types. A leading `change` in M101.007 and `unfold` in
M101.008 and M101.009 expose these proposition definitions. The private
prerequisites and their uses are renamed. The source proof bodies are
otherwise retained. The source `extensionSubgroup` abbreviation is
definitionally the target's Mathlib subgroup. This proves only the
specified NYLL support theorem.

The original copyright, authorship and Apache-2.0 header are retained.
The original license and notices remain in `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.

# NYLL extension fixed representation norm comparison

Worker 196, 14 November 2026.

## Source and correspondence

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`. Registered source
`nyll-classfieldtheory-fbd320cd-supplement`, content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The source module is
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FieldRepresentation.lean`,
SHA-256 `8124bbdd42702e1dba3060f8a2f14c6d66ead33c113d0b4310bc6157fea19bb9`.
The original copyright and author header is retained. The Library retains
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.

| Unit | Source theorem and type lines | Adapted declaration |
| --- | --- | --- |
| M073.005 | `ClassFormation.extensionFixedRepresentation_norm_coe`, 104–116 | `Langlands.NYLL.ClassFormation.extensionFixedRepresentation_norm_coeStatement` |

## Statement and complete telescope

The implicit group parameter is `{G : IntegralRepGroupType}`, with `[Group G]`
and `[TopologicalSpace G]`, as in source line 31. In order, the explicit
parameters are `A : Rep ℤ G`, `K L : ClosedSubgroup G`, the containment
`hLK : L.toSubgroup ≤ K.toSubgroup` and the normality witness `hnormal`.
These are followed by the source instance binder `[Finite (K/L)]` and final
explicit `a : (extensionFixedRepresentation A K L hLK hnormal).V`.
The published `IntegralRepGroupType` is `Type 0`; the representation and all
other universe constraints are those of the unchanged source objects.

The proposition first installs `hnormal` with `letI`, then the `Fintype`
instance `Fintype.ofFinite (K/L)`. It equates the underlying ambient vector
of the representation norm applied to `a` with the underlying vector of
`relativeNorm A K L hLK` applied to
`extensionFixedRepresentationEquiv A K L hLK hnormal a`. The left side is
exactly `((extensionFixedRepresentation A K L hLK hnormal).norm.hom a).1`;
the right side retains both source coercions through `ambientFixedAddSubgroup A K`
and `A.V`.

The coefficient representation, carrier equivalence and relative norm are
the actual published constructions. In particular, the relative norm is the
coset sum with fixedness established in its construction. No chosen maps or
extra hypotheses replace these objects. This file records a proposition and
provides no proof of its equality.

## Modifications and published dependencies

Prefix `ClassFormation` by `Langlands.NYLL`, append `Statement`, and replace
the theorem declaration by a `def ... : Prop` whose body is the entire
source theorem type. Omit the source proof at lines 117–139. Preserve the
noncomputable section, complete telescope, binder kinds, two local instances
and both sides of the equality. No global instance is added.

Expand `CyclicCohomology.extensionSubgroup K L hLK` to the exact abbreviation
body `L.toSubgroup.subgroupOf K.toSubgroup`, from the same pinned source's
`Nyll/GaloisCohomology/Cyclic/NormKernelVanishing.lean:47–54`.
The containment witness remains explicit. Replace the broad source imports
by the two focused published modules listed in the Lean file:
`FieldRepresentation.FixedCarrier.Definitions` supplies M073.001, and
`Degree.Norm.RelativeNorm.Definitions` supplies M024.009. These reuse the
published quotient representation and pointwise fixed subgroup.
Unused scope openings and the broad module introduction are omitted.

## Verification and scope

The private source comparison reconstructs the complete source statement
using the original `extensionSubgroup` abbreviation and checks equality of
the entire unapplied proposition definitions by `rfl`. The development
check and exact Prop inspection use environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean v4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`). Source comparison `6c51d515-a18c-45a4-a84a-b3808ffc13d7` and exact
inspection `9e4e6893-156b-4c53-9cf3-9c204c710696` both finished with zero
errors and warnings; the inspection reports `statement_returns_prop: true`
and no universe parameters, matching the source objects. Development checks do not supply
independent semantic acceptance or a proof of this target. Proofs remain
separate `lean.proof@1` work.

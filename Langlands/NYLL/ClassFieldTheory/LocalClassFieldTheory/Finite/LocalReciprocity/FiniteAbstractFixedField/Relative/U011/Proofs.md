# NYLL M099.011: normality of the relative fixing subgroup

This module proves the published Library proposition
`Langlands.NYLL.LocalClassFieldTheory.abstractRelativeFixingSubgroup_normalStatement`
by the theorem
`Langlands.NYLL.LocalClassFieldTheory.abstractRelativeFixingSubgroup_normal`.
The theorem's type is exactly that proposition applied to its source
parameters, `abstractRelativeFixingSubgroup_normalStatement k Ω K L hLK hnormal`.

Its direct imports are the published statement module
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Relative.Statements`
and the published proof module
`...FiniteAbstractFixedField.Relative.U010.Proofs` (M099.010). These
published files and their complete imported chains remain unchanged.

## Target and parameters

The theorem has, in this order, explicit `k Ω : Type`, the instances
`[Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]`, explicit closed subgroups
`K L : ClosedSubgroup (Gal(Ω/k))`, an explicit inclusion
`hLK : L.toSubgroup ≤ K.toSubgroup` and an explicit normality witness
`hnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal`. The Galois
extension `Ω/k` may be infinite.

Unfolding the published proposition gives

```lean
(abstractRelativeFixedField k Ω hLK).fixingSubgroup.Normal
```

that is, the subgroup of `Gal(Ω/Fix K)` fixing the fixed field `Fix L` of
`L`, regarded over `Fix K`, is normal. The hypothesis says that `L`, viewed
as a subgroup of `K`, is normal. The theorem transfers this relative
normality of the abstract subgroups to the concrete fixing subgroup.

## Implemented proof

The complete proof body is

```lean
  have hmap : ((L.toSubgroup.subgroupOf K.toSubgroup).map
      (abstractSubgroupEquivGaloisGroup k Ω K).toMonoidHom).Normal :=
    hnormal.map (abstractSubgroupEquivGaloisGroup k Ω K).toMonoidHom
      (abstractSubgroupEquivGaloisGroup k Ω K).surjective
  rw [map_extensionSubgroup_abstractSubgroupEquiv k Ω K L hLK] at hmap
  exact hmap
```

Mathlib's `Subgroup.Normal.map` says that the image of a normal subgroup under
a surjective homomorphism is normal. Applied to `hnormal` and the published
equivalence `abstractSubgroupEquivGaloisGroup k Ω K : K.toSubgroup ≃* Gal(Ω/Fix K)`,
which is surjective, it gives `hmap`. The published M099.010 theorem
`map_extensionSubgroup_abstractSubgroupEquiv k Ω K L hLK` identifies that
image with `(abstractRelativeFixedField k Ω hLK).fixingSubgroup`; rewriting
`hmap` with it gives exactly the stated normality.

The source proof writes `extensionSubgroup K L hLK` in the hypothesis
`hnormal` and in `hmap`; following the published proposition, both are
written with its body `L.toSubgroup.subgroupOf K.toSubgroup` (M004.002, an
`abbrev`). Apart from this and stating the type as the published
proposition, this is the original proof verbatim. No auxiliary declaration,
extra hypothesis, instance or `simp` registration is introduced. The
development check reports only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Actual dependencies

- The published proposition
  `Langlands.NYLL.LocalClassFieldTheory.abstractRelativeFixingSubgroup_normalStatement`
  in FiniteAbstractFixedField.Relative.Statements.
- The published theorem
  `Langlands.NYLL.LocalClassFieldTheory.map_extensionSubgroup_abstractSubgroupEquiv`
  (M099.010, FiniteAbstractFixedField.Relative.U010.Proofs).
- The published definitions `abstractRelativeFixedField`
  (FiniteAbstractFixedField.Relative.Definitions) and
  `abstractSubgroupEquivGaloisGroup`
  (FiniteAbstractFixedField.Initial.Definitions), reached through the
  unchanged Statements import chain.
- Mathlib's `Subgroup.Normal.map` (`Mathlib/Algebra/Group/Subgroup/Basic.lean`),
  `MulEquiv.toMonoidHom` and `MulEquiv.surjective`.

No host class-formation or reciprocity theorem is used.

## Pinned source and declaration map

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteAbstractFixedField.lean:167–180`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteAbstractFixedField.lean#L167-L180).
Lines 167–169 are the retained docstring (its words are kept, with the
source's line break inside "subgroup fixing" removed), 170–174 the signature
and 175–180 the proof. The section variables are
`(k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]` at line 31.
The
[public partition](../../../../../../../../../notes/reuse/nyll-public-port/m097-m120.md#m099)
places this proof at M099.011 (source unit lines 170–183) after M099.010.END.
The whole-file SHA-256 is
`d5fcb8f064a049b7d0af4268dd80f08f5c5e8b319d91164b57e4e989760191c5`,
recomputed by Worker 96 on 13 November 2026 UTC from the retained snapshot.

| Original | Adapted in `Langlands.NYLL.LocalClassFieldTheory` |
| --- | --- |
| Asserted type of `LocalClassFieldTheory.abstractRelativeFixingSubgroup_normal` (M099.011) | Published `abstractRelativeFixingSubgroup_normalStatement` in FiniteAbstractFixedField.Relative.Statements |
| Proof `LocalClassFieldTheory.abstractRelativeFixingSubgroup_normal` | This theorem of the same adapted name in FiniteAbstractFixedField.Relative.U011.Proofs |
| `LocalClassFieldTheory.map_extensionSubgroup_abstractSubgroupEquiv` (M099.010) | Published theorem in FiniteAbstractFixedField.Relative.U010.Proofs |
| `CyclicCohomology.extensionSubgroup K L hLK` | Its body `L.toSubgroup.subgroupOf K.toSubgroup` |

The adaptation prefixes the namespace with `Langlands.NYLL`, replaces the
original imports by the published Relative.Statements and Relative.U010.Proofs
imports, opens only `RamificationTheory` (the source also opens
`KummerTheory`, `CyclicCohomology`, `ClassFormation` and a
`noncomputable section`, unused here), and states the theorem's type as the
published proposition applied to `k Ω K L hLK hnormal`.

The retained source is registered as
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

## Attribution, environment and scope

The Lean file retains the original 2026 Naganori Yamaguchi copyright,
Apache-2.0 and author header verbatim, including “Naganori Yamaguchi
(assisted by OpenAI Codex)”, followed by Worker 96's dated modification
record. Worker 96 extracted this proof directly from the pinned original and
the published statement. No unpublished project draft was reused, and there
are no project coauthors.

The unchanged inherited
[LICENSE](../../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../../licenses/NYLL/NOTICE) are retained, with
SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`
respectively.

The approved environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096`:
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
Development compilation is separate from acceptance. Publication under
`lean.proof@1` requires the Lake build, kernel and exact-target checks,
unchanged statement and dependency checks, independent semantic review and
Integrator publication.

This proof covers only M099.011. It provides a normality theorem from an
explicit witness, not an instance. The Galois property of the relative fixed
field (M099.012) and any host class-formation, cup, transfer, Tate or
reciprocity target are separate work.

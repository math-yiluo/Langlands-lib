# NYLL M099.010: image of the relative subgroup under the abstract Galois equivalence

This module proves the published Library proposition
`Langlands.NYLL.LocalClassFieldTheory.map_extensionSubgroup_abstractSubgroupEquivStatement`
by the theorem
`Langlands.NYLL.LocalClassFieldTheory.map_extensionSubgroup_abstractSubgroupEquiv`.
The theorem's type is exactly that proposition applied to its source
parameters, `map_extensionSubgroup_abstractSubgroupEquivStatement k Ω K L hLK`.

Its sole direct import is
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Relative.Statements`.
That published Lean/Markdown pair and its complete imported chain remain
unchanged.

## Target and parameters

The theorem has, in this order, explicit `k Ω : Type`, the instances
`[Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]`, explicit closed subgroups
`K L : ClosedSubgroup (Gal(Ω/k))` and an explicit inclusion
`hLK : L.toSubgroup ≤ K.toSubgroup`. The Galois extension `Ω/k` may be
infinite; no finiteness, openness or local-field hypothesis is assumed.

Unfolding the published proposition gives

```lean
(L.toSubgroup.subgroupOf K.toSubgroup).map
    (abstractSubgroupEquivGaloisGroup k Ω K).toMonoidHom =
  (abstractRelativeFixedField k Ω hLK).fixingSubgroup
```

Here `abstractFixedField k Ω H` is the published fixed field
`IntermediateField.fixedField H.toSubgroup`;
`abstractSubgroupEquivGaloisGroup k Ω K : K.toSubgroup ≃* Gal(Ω/abstractFixedField k Ω K)`
is the published equivalence, the composite of the subgroup congruence along
Mathlib's `InfiniteGalois.fixingSubgroup_fixedField K` with
`IntermediateField.fixingSubgroupEquiv`, so that an element `σ` acts on `Ω`
as `σ.1`; and `abstractRelativeFixedField k Ω hLK` is the fixed field of `L`
regarded as an intermediate field of `Ω` over the fixed field of `K`. The
statement says that the equivalence carries `L`, viewed as a subgroup of `K`,
onto the subgroup of `Gal(Ω/Fix K)` fixing `Fix L`.

## Implemented proof

The proof applies `ext τ` (directly to the stated type) and proves both
inclusions.

Image into fixing subgroup: for `τ` the image of `σ : K.toSubgroup` with
`hσ : σ ∈ L.toSubgroup.subgroupOf K.toSubgroup`, the goal is rewritten by
`IntermediateField.mem_fixingSubgroup_iff`, and for `x ∈ Fix L` it must be
shown that the image of `σ` fixes `x`, which unfolds to `σ.1 x = x`. Mathlib's
`Subgroup.mem_subgroupOf` turns `hσ` into `hσL : σ.1 ∈ L.toSubgroup`. Then
`σ.1 ∈ (abstractFixedField k Ω L).fixingSubgroup` follows by rewriting with
the infinite Galois correspondence `InfiniteGalois.fixingSubgroup_fixedField L`
(`(IntermediateField.fixedField L.toSubgroup).fixingSubgroup = L.toSubgroup`
for closed `L`, using `[IsGalois k Ω]`), and
`IntermediateField.mem_fixingSubgroup_iff` gives that `σ.1` fixes every
element of `Fix L`, in particular `x`.

Fixing subgroup into image: given `hτ`, that `τ` fixes `Fix L`, let
`σ := (abstractSubgroupEquivGaloisGroup k Ω K).symm τ`. The witness is `σ`,
with image `τ` by `MulEquiv.apply_symm_apply`. Membership
`σ ∈ L.toSubgroup.subgroupOf K.toSubgroup` is reduced by
`Subgroup.mem_subgroupOf` to `σ.1 ∈ L.toSubgroup`. The proof shows that
`σ.1` fixes every `x ∈ Fix L` by the calculation

```lean
      calc
        σ.1 x = abstractSubgroupEquivGaloisGroup k Ω K σ x := rfl
        _ = τ x := by
          rw [show abstractSubgroupEquivGaloisGroup k Ω K σ = τ by
            exact (abstractSubgroupEquivGaloisGroup k Ω K).apply_symm_apply τ]
        _ = x := hτfix
```

where `hτfix` comes from `hτ` and `IntermediateField.mem_fixingSubgroup_iff`.
The first step holds by definition of the equivalence. Rewriting the
resulting membership in `(abstractFixedField k Ω L).fixingSubgroup` by
`InfiniteGalois.fixingSubgroup_fixedField L` gives `σ.1 ∈ L.toSubgroup`.

### Differences from the source proof

The source proof is followed step by step, with three replacements of
unpublished source lemmas by their definitional content:

- The source states the target with `CyclicCohomology.extensionSubgroup K L hLK`;
  the published proposition uses its body
  `L.toSubgroup.subgroupOf K.toSubgroup` (M004.002, an `abbrev`).
- Source lines 137–138 and 150 use `KummerTheory.mem_extensionSubgroup_iff`
  (M022.001), which is not published and whose source proof is `Iff.rfl`
  (`Nyll/GaloisCohomology/Kummer/Abstract/KummerAbelianAssembly.lean`,
  lines 33–38). As the task contract directs, they use Mathlib's
  `Subgroup.mem_subgroupOf` instead, and `hσL` is stated as membership in
  `L.toSubgroup` rather than in the closed subgroup `L`.
- Source lines 158–159 justify the first calc step by
  `(abstractSubgroupEquivGaloisGroup_apply k Ω K σ x).symm` (M099.008), which
  is published in `FiniteAbstractFixedField/Initial/U008/Proofs.lean` and has
  source proof `rfl`; the step here is directly `rfl`.

No auxiliary declaration, extra hypothesis, instance or `simp` registration is
introduced, and no copy of these lemmas is made. The development
check reports only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Actual dependencies

- The published proposition
  `Langlands.NYLL.LocalClassFieldTheory.map_extensionSubgroup_abstractSubgroupEquivStatement`
  in FiniteAbstractFixedField.Relative.Statements.
- The published definitions `abstractRelativeFixedField`
  (FiniteAbstractFixedField.Relative.Definitions), `abstractFixedField` and
  `abstractSubgroupEquivGaloisGroup` (FiniteAbstractFixedField.Initial.Definitions)
  in `Langlands.NYLL.LocalClassFieldTheory`, reached through the unchanged
  Statements import chain.
- Mathlib's `InfiniteGalois.fixingSubgroup_fixedField`
  (`Mathlib/FieldTheory/Galois/Infinite.lean`),
  `IntermediateField.mem_fixingSubgroup_iff`
  (`Mathlib/FieldTheory/Galois/Basic.lean`), `Subgroup.mem_subgroupOf`
  (`Mathlib/Algebra/Group/Subgroup/Map.lean`) and
  `MulEquiv.apply_symm_apply`; membership in `Subgroup.map` is destructed
  and constructed definitionally by `rintro` and the anonymous-constructor
  witness.

No host class-formation or reciprocity theorem is used.

## Pinned source and declaration map

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteAbstractFixedField.lean:124–165`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteAbstractFixedField.lean#L124-L165).
Lines 124–125 are the retained docstring, 126–131 the signature, 132–145 the
first inclusion and 146–165 the second. The section variables are
`(k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]` at line 31.
The
[public partition](../../../../../../../../../notes/reuse/nyll-public-port/m097-m120.md#m099)
places this proof at M099.010 (source unit lines 126–169) after M099.009.END.
The whole-file SHA-256 is
`d5fcb8f064a049b7d0af4268dd80f08f5c5e8b319d91164b57e4e989760191c5`,
recomputed by Worker 96 on 13 November 2026 UTC from the retained snapshot.

| Original | Adapted in `Langlands.NYLL.LocalClassFieldTheory` |
| --- | --- |
| Asserted type of `LocalClassFieldTheory.map_extensionSubgroup_abstractSubgroupEquiv` (M099.010) | Published `map_extensionSubgroup_abstractSubgroupEquivStatement` in FiniteAbstractFixedField.Relative.Statements |
| Proof `LocalClassFieldTheory.map_extensionSubgroup_abstractSubgroupEquiv` | This theorem of the same adapted name in FiniteAbstractFixedField.Relative.U010.Proofs |
| `CyclicCohomology.extensionSubgroup K L hLK` | Its body `L.toSubgroup.subgroupOf K.toSubgroup` |
| `KummerTheory.mem_extensionSubgroup_iff` (M022.001, `Iff.rfl`) | Mathlib's `Subgroup.mem_subgroupOf` |
| `LocalClassFieldTheory.abstractSubgroupEquivGaloisGroup_apply` (M099.008, `rfl`) | `rfl` |

The adaptation prefixes the namespace with `Langlands.NYLL`, replaces the
original imports by the sole published Relative.Statements import, opens only
`RamificationTheory` (the source also opens `KummerTheory`,
`CyclicCohomology`, `ClassFormation` and a `noncomputable section`, unused
here), states the theorem's type as the published proposition applied to
`k Ω K L hLK`, and makes the replacements above.

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

This proof covers only M099.010. The normality transfer M099.011, the Galois
property of the relative fixed field and any host class-formation, cup,
transfer, Tate or reciprocity target are separate work.

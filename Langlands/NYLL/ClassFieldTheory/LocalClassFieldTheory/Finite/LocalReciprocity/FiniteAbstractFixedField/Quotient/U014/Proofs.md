# NYLL M099.014: kernel of the relative quotient homomorphism

This module proves the published Library proposition
`Langlands.NYLL.LocalClassFieldTheory.abstractRelativeToAmbientQuotient_kerStatement`
by the theorem
`Langlands.NYLL.LocalClassFieldTheory.abstractRelativeToAmbientQuotient_ker`.
The theorem's type is exactly that proposition applied to its source
parameters, `abstractRelativeToAmbientQuotient_kerStatement k Ω K L hLK hnormal`.

Its sole direct import is
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Quotient.Statements`.
That published Lean/Markdown pair and its complete imported chain remain
unchanged.

## Target and parameters

The theorem has, in this order, explicit `k Ω : Type`, the instances
`[Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]`, explicit closed subgroups
`K L : ClosedSubgroup (Gal(Ω/k))`, an explicit inclusion
`hLK : L.toSubgroup ≤ K.toSubgroup` and an explicit relative normality
hypothesis `hnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal`. The
Galois extension `Ω/k` may be infinite; no finiteness, openness or
local-field hypothesis is assumed.

Unfolding the published proposition gives

```lean
letI : (abstractRelativeFixedField k Ω hLK).fixingSubgroup.Normal :=
  abstractRelativeFixingSubgroup_normal k Ω K L hLK hnormal
(abstractRelativeToAmbientQuotient k Ω K L hLK hnormal).ker =
  L.toSubgroup.subgroupOf K.toSubgroup
```

Here `abstractRelativeToAmbientQuotient k Ω K L hLK hnormal` is the published
homomorphism (M099.013)
`K.toSubgroup →* Gal(Ω/abstractFixedField k Ω K) ⧸ (abstractRelativeFixedField k Ω hLK).fixingSubgroup`,
the composite of the published equivalence
`abstractSubgroupEquivGaloisGroup k Ω K : K.toSubgroup ≃* Gal(Ω/abstractFixedField k Ω K)`
with the quotient map `QuotientGroup.mk'` by the subgroup of
`Gal(Ω/Fix K)` fixing `Fix L`, whose normality is the published theorem
`abstractRelativeFixingSubgroup_normal` (M099.011). The statement says that
the kernel of this map is `L`, viewed as a subgroup of `K`.

## Implemented proof

```lean
  let : (abstractRelativeFixedField k Ω hLK).fixingSubgroup.Normal :=
    abstractRelativeFixingSubgroup_normal k Ω K L hLK hnormal
  ext σ
  change
    QuotientGroup.mk' (abstractRelativeFixedField k Ω hLK).fixingSubgroup
        (abstractSubgroupEquivGaloisGroup k Ω K σ) = 1 ↔
      σ ∈ L.toSubgroup.subgroupOf K.toSubgroup
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  rw [← map_extensionSubgroup_abstractSubgroupEquiv k Ω K L hLK]
  constructor
  · rintro ⟨τ, hτ, hτσ⟩
    have : τ = σ :=
      (abstractSubgroupEquivGaloisGroup k Ω K).injective hτσ
    simpa [this] using hτ
  · intro hσ
    exact ⟨σ, hσ, rfl⟩
```

1. The first line installs, as a local instance, the normality of the upper
   fixing subgroup given by the published M099.011 theorem
   `abstractRelativeFixingSubgroup_normal k Ω K L hLK hnormal`, with the same
   type annotation as the published statement. This is the instance used by
   the quotient group structure in the statement.
2. `ext σ` reduces the subgroup equality (directly on the stated type) to
   membership of an arbitrary `σ : K.toSubgroup`.
3. `change` restates the left-hand membership in the kernel definitionally:
   `σ` is in the kernel of the composite exactly when the quotient class of
   `abstractSubgroupEquivGaloisGroup k Ω K σ` is `1`.
4. Mathlib's `QuotientGroup.mk'_apply` and `QuotientGroup.eq_one_iff` turn
   this into membership of `abstractSubgroupEquivGaloisGroup k Ω K σ` in
   `(abstractRelativeFixedField k Ω hLK).fixingSubgroup`.
5. Rewriting backwards with the published M099.010 theorem
   `map_extensionSubgroup_abstractSubgroupEquiv k Ω K L hLK` replaces that
   fixing subgroup by the image of `L.toSubgroup.subgroupOf K.toSubgroup`
   under the equivalence.
6. Forward direction: membership in the image (Mathlib's `Subgroup.mem_map`,
   destructed definitionally by `rintro`) gives `τ` in the relative subgroup
   with the same image as `σ`; injectivity of the equivalence
   (`MulEquiv.injective`) gives `τ = σ`, and `simpa [this] using hτ` closes
   the goal. Backward direction: `σ` itself is a witness, with image equality
   `rfl`.

### Differences from the source proof

The source proof (lines 219–234) is followed tactic by tactic. The only
change is that the source's `CyclicCohomology.extensionSubgroup K L hLK`
(M004.002, an `abbrev` whose body is `L.toSubgroup.subgroupOf K.toSubgroup`,
`Nyll/GaloisCohomology/Cyclic/NormKernelVanishing.lean:47–54`) is written as
that Mathlib body in the stated type and in the `change` target, as in the
published statement and the published M099.010 and M099.011 ports.

No auxiliary declaration, extra hypothesis, global instance or `simp`
registration is introduced. The development check (diagnostics
`0e157925-5a9e-40f0-88ae-82d2a086869f`, 0 errors and 0 warnings) reports only
the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Actual dependencies

- The published proposition
  `Langlands.NYLL.LocalClassFieldTheory.abstractRelativeToAmbientQuotient_kerStatement`
  in FiniteAbstractFixedField.Quotient.Statements.
- The published definition `abstractRelativeToAmbientQuotient`
  (FiniteAbstractFixedField.Quotient.Definitions), the published theorems
  `abstractRelativeFixingSubgroup_normal` (M099.011,
  FiniteAbstractFixedField.Relative.U011.Proofs) and
  `map_extensionSubgroup_abstractSubgroupEquiv` (M099.010,
  FiniteAbstractFixedField.Relative.U010.Proofs), and the published
  definitions `abstractRelativeFixedField`, `abstractFixedField` and
  `abstractSubgroupEquivGaloisGroup`, all in
  `Langlands.NYLL.LocalClassFieldTheory` and reached through the unchanged
  Statements import chain.
- Mathlib's `QuotientGroup.mk'_apply` and `QuotientGroup.eq_one_iff`
  (`Mathlib/GroupTheory/QuotientGroup/Defs.lean`), `MulEquiv.injective`
  (`Mathlib/Algebra/Group/Equiv/Defs.lean`), and the definitional
  characterizations of `MonoidHom.ker` membership and `Subgroup.map`
  membership (`Subgroup.mem_map`, `Mathlib/Algebra/Group/Subgroup/Map.lean`,
  `Iff.rfl`) used by `change`, `rintro` and the anonymous-constructor witness.

No host class-formation or reciprocity theorem is used.

## Pinned source and declaration map

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteAbstractFixedField.lean:212–234`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteAbstractFixedField.lean#L212-L234).
Lines 212–218 are the signature and 219–234 the proof; the retained docstring
is lines 210–211. The section variables are
`(k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]` at line 31.
The
[public partition](../../../../../../../../../notes/reuse/nyll-public-port/m097-m120.md#m099)
places this proof at M099.014 (source unit lines 212–236, line 236 being the
docstring of the next theorem) after M099.013.END. The whole-file SHA-256 is
`d5fcb8f064a049b7d0af4268dd80f08f5c5e8b319d91164b57e4e989760191c5`,
recomputed by Worker 4913 on 14 November 2026 UTC from the retained snapshot.

| Original | Adapted in `Langlands.NYLL.LocalClassFieldTheory` |
| --- | --- |
| Asserted type of `LocalClassFieldTheory.abstractRelativeToAmbientQuotient_ker` (M099.014) | Published `abstractRelativeToAmbientQuotient_kerStatement` in FiniteAbstractFixedField.Quotient.Statements |
| Proof `LocalClassFieldTheory.abstractRelativeToAmbientQuotient_ker` | This theorem of the same adapted name in FiniteAbstractFixedField.Quotient.U014.Proofs |
| `CyclicCohomology.extensionSubgroup K L hLK` | Its body `L.toSubgroup.subgroupOf K.toSubgroup` |

The adaptation prefixes the namespace with `Langlands.NYLL`, replaces the
original imports by the sole published Quotient.Statements import, opens only
`RamificationTheory` (the source also opens `KummerTheory`,
`CyclicCohomology`, `ClassFormation` and a `noncomputable section`, unused
here), states the theorem's type as the published proposition applied to
`k Ω K L hLK hnormal`, and makes the replacement above.

The retained source is registered as
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

## Attribution, environment and scope

The Lean file retains the original 2026 Naganori Yamaguchi copyright,
Apache-2.0 and author header verbatim, including “Naganori Yamaguchi
(assisted by OpenAI Codex)”, followed by Worker 4913's dated modification
record. Worker 4913 extracted this proof directly from the pinned original and
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

This proof covers only M099.014. The surjectivity M099.015, the quotient
equivalences M099.016/M099.017 and any host class-formation, cup, transfer,
Tate or reciprocity target are separate work.

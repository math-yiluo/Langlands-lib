# NYLL M099.015: surjectivity of the relative quotient homomorphism

This module proves the published Library proposition
`Langlands.NYLL.LocalClassFieldTheory.abstractRelativeToAmbientQuotient_surjectiveStatement`
by the theorem
`Langlands.NYLL.LocalClassFieldTheory.abstractRelativeToAmbientQuotient_surjective`.
The theorem's type is exactly that proposition applied to its source
parameters,
`abstractRelativeToAmbientQuotient_surjectiveStatement k Ω K L hLK hnormal`.

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
Function.Surjective
  (abstractRelativeToAmbientQuotient k Ω K L hLK hnormal)
```

Here `abstractRelativeToAmbientQuotient k Ω K L hLK hnormal` is the published
homomorphism (M099.013)
`K.toSubgroup →* Gal(Ω/abstractFixedField k Ω K) ⧸ (abstractRelativeFixedField k Ω hLK).fixingSubgroup`,
the composite of the published equivalence
`abstractSubgroupEquivGaloisGroup k Ω K : K.toSubgroup ≃* Gal(Ω/abstractFixedField k Ω K)`
with the quotient map by the subgroup of `Gal(Ω/Fix K)` fixing `Fix L`, whose
normality is the published theorem `abstractRelativeFixingSubgroup_normal`
(M099.011). The statement says that every class in this quotient is the image
of an element of `K`.

## Implemented proof

```lean
  let : (abstractRelativeFixedField k Ω hLK).fixingSubgroup.Normal :=
    abstractRelativeFixingSubgroup_normal k Ω K L hLK hnormal
  intro q
  refine Quotient.inductionOn' q ?_
  intro τ
  refine ⟨(abstractSubgroupEquivGaloisGroup k Ω K).symm τ, ?_⟩
  change QuotientGroup.mk
    (abstractSubgroupEquivGaloisGroup k Ω K
      ((abstractSubgroupEquivGaloisGroup k Ω K).symm τ)) =
      QuotientGroup.mk τ
  rw [(abstractSubgroupEquivGaloisGroup k Ω K).apply_symm_apply]
```

1. The first line installs, as a local instance, the normality of the upper
   fixing subgroup given by the published M099.011 theorem
   `abstractRelativeFixingSubgroup_normal k Ω K L hLK hnormal`, with the same
   type annotation as the published statement.
2. `intro q` takes an arbitrary class `q` of the quotient (the stated type
   unfolds to `∀ q, ∃ σ, abstractRelativeToAmbientQuotient … σ = q`).
3. Mathlib's `Quotient.inductionOn'` reduces to a class
   `QuotientGroup.mk τ` of a representative `τ : Gal(Ω/abstractFixedField k Ω K)`.
4. The preimage is `(abstractSubgroupEquivGaloisGroup k Ω K).symm τ`.
5. `change` restates the image of this preimage definitionally as the
   quotient class of `abstractSubgroupEquivGaloisGroup k Ω K` applied to it,
   and rewriting with `MulEquiv.apply_symm_apply` turns the goal into
   `QuotientGroup.mk τ = QuotientGroup.mk τ`, closed by `rw`'s `rfl`.

### Differences from the source proof

The source proof (lines 244–254) is reproduced verbatim. The only adaptation
is in the stated type: the source hypothesis
`(CyclicCohomology.extensionSubgroup K L hLK).Normal` appears as
`(L.toSubgroup.subgroupOf K.toSubgroup).Normal`, the Mathlib body of that
`abbrev` (M004.002, `Nyll/GaloisCohomology/Cyclic/NormKernelVanishing.lean:47–54`),
as in the published statement.

No auxiliary declaration, extra hypothesis, global instance or `simp`
registration is introduced. The development check (diagnostics
`9ecb32d4-3282-4bbb-9273-a4b97064eb31`, 0 errors and 0 warnings) reports only
the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Actual dependencies

- The published proposition
  `Langlands.NYLL.LocalClassFieldTheory.abstractRelativeToAmbientQuotient_surjectiveStatement`
  in FiniteAbstractFixedField.Quotient.Statements.
- The published definition `abstractRelativeToAmbientQuotient`
  (FiniteAbstractFixedField.Quotient.Definitions), the published theorem
  `abstractRelativeFixingSubgroup_normal` (M099.011,
  FiniteAbstractFixedField.Relative.U011.Proofs), and the published
  definitions `abstractRelativeFixedField`, `abstractFixedField` and
  `abstractSubgroupEquivGaloisGroup`, all in
  `Langlands.NYLL.LocalClassFieldTheory` and reached through the unchanged
  Statements import chain.
- Mathlib's `Quotient.inductionOn'` (`Mathlib/Data/Quot.lean`) and
  `MulEquiv.apply_symm_apply` (`Mathlib/Algebra/Group/Equiv/Defs.lean`).

No host class-formation or reciprocity theorem is used.

## Pinned source and declaration map

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteAbstractFixedField.lean:237–254`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteAbstractFixedField.lean#L237-L254).
Lines 237–243 are the signature and 244–254 the proof; the retained docstring
is line 236. The section variables are
`(k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]` at line 31.
The
[public partition](../../../../../../../../../notes/reuse/nyll-public-port/m097-m120.md#m099)
places this proof at M099.015 (source unit lines 237–258, lines 256–258 being
the docstring of the next definition) after M099.014.END. The whole-file
SHA-256 is
`d5fcb8f064a049b7d0af4268dd80f08f5c5e8b319d91164b57e4e989760191c5`,
recomputed by Worker 4913 on 14 November 2026 UTC from the retained snapshot.

| Original | Adapted in `Langlands.NYLL.LocalClassFieldTheory` |
| --- | --- |
| Asserted type of `LocalClassFieldTheory.abstractRelativeToAmbientQuotient_surjective` (M099.015) | Published `abstractRelativeToAmbientQuotient_surjectiveStatement` in FiniteAbstractFixedField.Quotient.Statements |
| Proof `LocalClassFieldTheory.abstractRelativeToAmbientQuotient_surjective` | This theorem of the same adapted name in FiniteAbstractFixedField.Quotient.U015.Proofs |
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

This proof covers only M099.015. The kernel M099.014, the quotient
equivalences M099.016/M099.017 and any host class-formation, cup, transfer,
Tate or reciprocity target are separate work.

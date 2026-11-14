# NYLL M099.003: a finite abstract quotient gives a finite ambient Galois quotient

This module proves the published Library proposition
`Langlands.NYLL.LocalClassFieldTheory.ambientQuotientFiniteOfAbstractFiniteStatement`
by the theorem
`Langlands.NYLL.LocalClassFieldTheory.ambientQuotientFiniteOfAbstractFinite`.
The theorem's type is exactly that proposition applied to its source
parameters, `ambientQuotientFiniteOfAbstractFiniteStatement k Ω H hfinite`.

Its sole direct import is
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Finiteness.Statements`.
That published Lean/Markdown pair and its complete imported chain remain
unchanged.

## Target and parameters

The theorem has, in this order, the explicit fields `k Ω : Type` with
instances `[Field k] [Field Ω] [Algebra k Ω]` (the section's
`[IsGalois k Ω]` is omitted, as in the source and the statement), a closed
subgroup `H : ClosedSubgroup (Gal(Ω/k))` and the hypothesis

```lean
hfinite : Finite ((baseField (Gal(Ω/k))).toSubgroup ⧸
  extensionSubgroup (baseField (Gal(Ω/k))) H (le_baseField H))
```

that the quotient of the distinguished base subgroup (the whole group) by
`H`, viewed as a subgroup of it, is finite. It has no universe parameters.

Unfolding the published proposition gives

```lean
Finite (Gal(Ω/k) ⧸ H.toSubgroup)
```

## Implemented proof

The complete proof body is

```lean
  apply Nat.finite_of_card_ne_zero
  change H.toSubgroup.index ≠ 0
  rw [← Subgroup.relIndex_top_right]
  change (extensionSubgroup (baseField (Gal(Ω/k))) H
    (le_baseField H)).index ≠ 0
  exact @Subgroup.index_ne_zero_of_finite
    (baseField (Gal(Ω/k))).toSubgroup _
    (extensionSubgroup (baseField (Gal(Ω/k))) H (le_baseField H))
    hfinite
```

Mathlib's `Nat.finite_of_card_ne_zero` reduces finiteness of the quotient to
`Nat.card (Gal(Ω/k) ⧸ H.toSubgroup) ≠ 0`, which is definitionally
`H.toSubgroup.index ≠ 0` since `Subgroup.index H` is defined as
`Nat.card (G ⧸ H)`; the first `change` makes this explicit. Rewriting
backwards with `Subgroup.relIndex_top_right : H.relIndex ⊤ = H.index` turns
the goal into `H.toSubgroup.relIndex ⊤ ≠ 0`. By definition,
`relIndex H ⊤ = (H.subgroupOf ⊤).index`; the published `baseField G` has
underlying subgroup `⊤` and `extensionSubgroup K L hLK` is an abbreviation of
`L.toSubgroup.subgroupOf K.toSubgroup`, so the second `change` restates the
goal as the index of the abstract extension subgroup being nonzero.
Mathlib's `Subgroup.index_ne_zero_of_finite`, applied explicitly with the
ambient group `(baseField (Gal(Ω/k))).toSubgroup` and with `hfinite` as its
finiteness instance, closes the goal.

Apart from stating the type as the published proposition, this is the
original declaration verbatim, including its docstring and the
`omit [IsGalois k Ω] in` of source line 48. No auxiliary declaration, extra
hypothesis or instance is introduced. The development check reports no
errors or warnings and only the axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Actual dependencies

- The published proposition
  `Langlands.NYLL.LocalClassFieldTheory.ambientQuotientFiniteOfAbstractFiniteStatement`
  in FiniteAbstractFixedField.Finiteness.Statements.
- The published definitions `Langlands.NYLL.ClassFormation.baseField`
  (AbstractClassFieldTheory.Degree.Fields.Definitions) and
  `Langlands.NYLL.CyclicCohomology.extensionSubgroup`
  (GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions), and
  the published theorem `Langlands.NYLL.ClassFormation.le_baseField`
  (AbstractClassFieldTheory.Degree.Fields.U005.Proofs), which occur in the
  statement and the `change` steps; all are reached through the Statements
  module's imports.
- Mathlib's `Nat.finite_of_card_ne_zero`
  (`Mathlib/SetTheory/Cardinal/Finite.lean`), `Subgroup.index`,
  `Subgroup.relIndex`, `Subgroup.relIndex_top_right` and
  `Subgroup.index_ne_zero_of_finite` (`Mathlib/GroupTheory/Index.lean`).

No other proof and no host class-formation, cup, transfer, Tate or
reciprocity theorem is used.

## Pinned source and declaration map

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteAbstractFixedField.lean:48–64`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteAbstractFixedField.lean#L48-L64).
Line 48 is `omit [IsGalois k Ω] in`, 49–50 the docstring, 51–55 the
signature and 56–64 the proof. The section variable line 31 is
`(k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]`, inside
`namespace LocalClassFieldTheory` (line 22) with
`open RamificationTheory KummerTheory CyclicCohomology` (line 23),
`open ClassFormation` (25) and `noncomputable section` (29). The
[public partition](../../../../../../../../../notes/reuse/nyll-public-port/m097-m120.md#m099)
places this proof at M099.003 (source unit start line 51). The whole-file
SHA-256 is
`d5fcb8f064a049b7d0af4268dd80f08f5c5e8b319d91164b57e4e989760191c5`,
recomputed by Worker 395 on 14 November 2026 UTC from the retained snapshot.

| Original in `LocalClassFieldTheory` | Adapted in `Langlands.NYLL.LocalClassFieldTheory` |
| --- | --- |
| Asserted type of `ambientQuotientFiniteOfAbstractFinite` (M099.003) | Published `ambientQuotientFiniteOfAbstractFiniteStatement` in FiniteAbstractFixedField.Finiteness.Statements |
| Proof `ambientQuotientFiniteOfAbstractFinite` | This theorem of the same adapted name in FiniteAbstractFixedField.Finiteness.U003.Proofs |

The adaptation prefixes the namespace with `Langlands.NYLL`, replaces the
original imports by the sole published Statements import, merges the source's
namespace openings into `open CyclicCohomology ClassFormation` (omitting the
unused `RamificationTheory` and `KummerTheory`), keeps the
`noncomputable section`, the section variables, `omit [IsGalois k Ω] in` and
the docstring, and states the theorem's type as the published proposition
applied to `k Ω H hfinite`. The proof is unchanged.

The retained source is registered as
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

## Attribution, environment and scope

The Lean file retains the original 2026 Naganori Yamaguchi copyright,
Apache-2.0 and author header verbatim, including “Naganori Yamaguchi
(assisted by OpenAI Codex)”, followed by Worker 395's dated modification
record. Worker 395 extracted this proof directly from the pinned original and
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

This proof covers only M099.003. The openness and finite-dimensionality
units M099.004 and M099.005, which use this result, and any host
class-formation, cup, transfer, Tate or reciprocity target are separate work.

# NYLL M022.002: the quotient action on an invariant subtype at a representative

This module proves the published Library proposition
`Langlands.NYLL.KummerTheory.extensionFixedRepresentation_quotient_mk_apply_valStatement`
by the theorem
`Langlands.NYLL.KummerTheory.extensionFixedRepresentation_quotient_mk_apply_val`.
The theorem's type is exactly that proposition applied to its source
parameters,
`extensionFixedRepresentation_quotient_mk_apply_valStatement A K M hMK a k`,
with the normality instance `hnormal` supplied by instance resolution from
the theorem's own instance binder.

Its sole direct import is
`Langlands.NYLL.GaloisCohomology.Kummer.Abstract.KummerAbelianAssembly.U002.Statements`.
That published Lean/Markdown pair and its complete imported chain remain
unchanged.

## Target and parameters

The theorem has the implicit group `G : IntegralRepGroupType` (that is,
`Type 0`) with instances `[Group G] [TopologicalSpace G]`, and, in this
order, the explicit `A : Rep ℤ G`, closed subgroups `K M : ClosedSubgroup G`,
the containment `hMK : M.toSubgroup ≤ K.toSubgroup`, the instance binder
`[hnormal : (M.toSubgroup.subgroupOf K.toSubgroup).Normal]`, an element
`a` of the invariant subtype `(extensionFixedRepresentation A K M hMK hnormal).V`
(the elements of `A` fixed by `G_M`) and `k : K.toSubgroup`. It has no
universe parameters.

Unfolding the published proposition gives

```lean
((extensionFixedRepresentation A K M hMK hnormal).ρ
    ((QuotientGroup.mk' (M.toSubgroup.subgroupOf K.toSubgroup)) k) a).1 =
  A.ρ k.1 a.1
```

that is, the action of the class of `k` in `G_K / G_M` on `a ∈ A_M`, viewed
in `A`, is the ambient action of `k` on `a`.

## Implemented proof

The proof term is `rfl`. The published definition
`Langlands.NYLL.CyclicCohomology.extensionFixedRepresentation A K M hMK hnormal`
is Mathlib's `Rep.quotientToInvariants` of the restriction
`Rep.res K.toSubgroup.subtype A` by the normal subgroup
`extensionSubgroup K M hMK`, an abbreviation of
`M.toSubgroup.subgroupOf K.toSubgroup`. Mathlib defines
`Rep.quotientToInvariants` as `Rep.of (A.ρ.quotientToInvariants S)`, where
`Representation.quotientToInvariants ρ S = ofQuotient (toInvariants ρ S) S`
is the action on the `S`-invariants factored through the quotient map
(`Mathlib/RepresentationTheory/Invariants.lean`). At the class
`QuotientGroup.mk' _ k` it therefore reduces to the action of `k` on the
invariants, whose underlying value is the action of `k` in the restricted
representation, which is `A.ρ k.1`. Hence the left side reduces
definitionally to `A.ρ k.1 a.1`, and the statement definition unfolds to this
equality, so the kernel accepts `rfl`.

Apart from stating the type as the published proposition, this is the
original declaration verbatim, including its docstring and the `@[simp]`
attribute of source line 42. No auxiliary declaration, extra hypothesis or
instance is introduced. The development check reports no errors or warnings
and only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Actual dependencies

- The published proposition
  `Langlands.NYLL.KummerTheory.extensionFixedRepresentation_quotient_mk_apply_valStatement`
  in KummerAbelianAssembly.U002.Statements.
- The published definitions `Langlands.NYLL.CyclicCohomology.extensionSubgroup`
  and `Langlands.NYLL.CyclicCohomology.extensionFixedRepresentation`
  (`Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions`)
  and the universe abbreviation `IntegralRepGroupType`
  (`Langlands.NYLL.GaloisCohomology.Cyclic.IntegralRepUniverse`), all reached
  through the Statements module's imports.
- Mathlib's `Rep.quotientToInvariants`, `Representation.quotientToInvariants`,
  `Representation.ofQuotient`, `Rep.res` and `QuotientGroup.mk'`, used only
  through definitional unfolding.

No other proof and no host class-formation, cup, transfer, Tate or
reciprocity theorem is used.

## Pinned source and declaration map

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/GaloisCohomology/Kummer/Abstract/KummerAbelianAssembly.lean:40–51`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/GaloisCohomology/Kummer/Abstract/KummerAbelianAssembly.lean#L40-L51).
Lines 40–41 are the docstring, 42 the `@[simp]` attribute and 43–51 the
signature, ending with the proof `rfl` on line 51. The section variable
line 28 is `{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]`, with
`open CyclicCohomology` at line 22. The source writes the normal subgroup as
`extensionSubgroup (G := G) K M hMK`, which the published statement and this
theorem write as its definitional body
`M.toSubgroup.subgroupOf K.toSubgroup`. The
[public partition](../../../../../../../../notes/reuse/nyll-public-port/m001-m024.md#m022)
places this proof at M022.002 (source unit lines 43–54). The whole-file
SHA-256 is
`ca4ad38a7ed46fa029400e2c7718faf0587b4206731c82c8c45d6839b719f54c`,
recomputed by Worker 395 on 14 November 2026 UTC from the retained snapshot.

| Original in `KummerTheory` | Adapted in `Langlands.NYLL.KummerTheory` |
| --- | --- |
| Asserted type of `extensionFixedRepresentation_quotient_mk_apply_val` (M022.002) | Published `extensionFixedRepresentation_quotient_mk_apply_valStatement` in KummerAbelianAssembly.U002.Statements |
| Proof `extensionFixedRepresentation_quotient_mk_apply_val` | This theorem of the same adapted name in KummerAbelianAssembly.U002.U002.Proofs |

The adaptation prefixes the namespace with `Langlands.NYLL`, replaces the
original imports by the sole published Statements import, keeps
`open CyclicCohomology`, the `noncomputable section`, the section variables,
the docstring and `@[simp]`, writes the instance binder with the body of
`extensionSubgroup` as the published statement does, and states the theorem's
type as the published proposition applied to `A K M hMK a k`. The proof is
unchanged.

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
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) are retained, with
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

This proof covers only M022.002. The fixed-value criterion M022.003, the
later KummerAbelianAssembly units and any host class-formation, cup,
transfer, Tate or reciprocity target are separate work.

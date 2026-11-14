# NYLL M028.002: coercion of the fixed-field inclusion

This module proves the published Library proposition
`Langlands.NYLL.ClassFormation.fixedFieldInclusion_coeStatement` by the
theorem `Langlands.NYLL.ClassFormation.fixedFieldInclusion_coe`. The
theorem's type is exactly that proposition applied to its source parameters,
`fixedFieldInclusion_coeStatement A K L hLK a`.

Its sole direct import is
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements.Statements`.
That published Lean/Markdown pair and its complete imported chain remain
unchanged.

## Target and parameters

The theorem has the implicit group `G : IntegralRepGroupType` (that is,
`Type 0`) with instances `[Group G] [TopologicalSpace G]`, and the explicit
parameters `A : Rep ℤ G`, closed subgroups `K L : ClosedSubgroup G`, the
containment `hLK : L.toSubgroup ≤ K.toSubgroup` (the extension `L | K`) and
an element `a : ambientFixedAddSubgroup A K` of `A_K`. Like the statement, it
has one universe parameter, the carrier universe of `A`.

Unfolding the published proposition gives

```lean
((fixedFieldInclusion A K L hLK a : ambientFixedAddSubgroup A L) : A.V) = a.1
```

that is, the inclusion `A_K → A_L` does not change the underlying element of
`A`.

## Implemented proof

The proof term is `rfl`. The published definition
`Langlands.NYLL.ClassFormation.fixedFieldInclusion` (M028.001) is the
additive homomorphism whose `toFun` sends `a` to
`⟨a.1, fun l => a.2 ⟨l.1, hLK l.2⟩⟩`. Applying it to `a` and taking the
`AddSubgroup` coercion to `A.V` therefore reduces definitionally to `a.1`,
and the statement definition unfolds definitionally to this equality, so the
kernel accepts `rfl`.

Apart from stating the type as the published proposition, this is the
original declaration verbatim, including its docstring and the `@[simp]`
attribute of source line 42. No auxiliary declaration, extra hypothesis or
instance is introduced. The development check reports no errors or warnings
and only the axioms `propext` and `Quot.sound`.

## Actual dependencies

- The published proposition
  `Langlands.NYLL.ClassFormation.fixedFieldInclusion_coeStatement` in
  PrimeElements.Statements.
- Its published definitions `fixedFieldInclusion` (PrimeElements.Definitions,
  M028.001) and `Langlands.NYLL.KummerTheory.ambientFixedAddSubgroup`
  (KummerDelta.U001.Definitions), the latter being the additive subgroup
  `{a | ∀ h : H.toSubgroup, A.ρ h.1 a = a}` of `A.V`, both used only through
  definitional unfolding.

No other proof and no host class-formation, cup, transfer, Tate or
reciprocity theorem is used.

## Pinned source and declaration map

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/PrimeElements.lean:38–47`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/PrimeElements.lean#L38-L47).
Lines 38–41 are the docstring, 42 the `@[simp]` attribute, 43–46 the
signature and 47 the proof `rfl`. The section variables are
`{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]` at line 27 and
`{D : DegreeData G} {A : Rep ℤ G}` at line 28; the latter are not used by
this theorem, whose `A` is an explicit binder. The
[public partition](../../../../../../../notes/reuse/nyll-public-port/m025-m048.md#m028)
places this proof at M028.002 (source unit lines 43–49). The whole-file
SHA-256 is
`9b2f91f76898d32b4f6f556a6b628aa0c4cf40768f43423b15e81de22fadc4bf`,
recomputed by Worker 395 on 14 November 2026 UTC from the retained snapshot.

| Original in `ClassFormation` | Adapted in `Langlands.NYLL.ClassFormation` |
| --- | --- |
| Asserted type of `fixedFieldInclusion_coe` (M028.002) | Published `fixedFieldInclusion_coeStatement` in PrimeElements.Statements |
| Proof `fixedFieldInclusion_coe` | This theorem of the same adapted name in PrimeElements.U002.Proofs |

The adaptation prefixes the namespace with `Langlands.NYLL`, replaces the
original import by the sole published Statements import, omits the unused
`open CyclicCohomology` and the unused section variable line 28, keeps
`open KummerTheory`, the `noncomputable section`, the variable line 27 with
its comment, the docstring and `@[simp]`, and states the theorem's type as the
published proposition applied to `A K L hLK a`. The proof is unchanged.

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
[LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) are retained, with
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

This proof covers only M028.002. The relative-norm identity M028.003 and any
host class-formation, cup, transfer, Tate or reciprocity target are separate
work.

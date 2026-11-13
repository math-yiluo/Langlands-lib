# NYLL M088.004: Galois-fixed ambient units

This module proves the published Library proposition
`Langlands.NYLL.LocalClassFieldTheory.mem_galoisAmbientUnits_fixed_iffStatement`
by the theorem
`Langlands.NYLL.LocalClassFieldTheory.mem_galoisAmbientUnits_fixed_iff`.
The theorem's type is exactly that proposition applied to its source
parameters, `mem_galoisAmbientUnits_fixed_iffStatement K Ω E x`.

Its sole direct import is
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbsoluteUnitsFixedField.FixedUnits.Statements`.
That published Lean/Markdown pair and its complete imported chain remain
unchanged.

## Target and parameters

The theorem has, in this order, explicit `K Ω : Type`, the instances
`[Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]`, an explicit intermediate
field `E : IntermediateField K Ω` and an explicit `x : Additive Ωˣ`. The
extension `Ω/K` may be infinite. No finite-dimensional, perfectness or
local-field hypothesis is assumed.

Unfolding the published proposition gives

```lean
x ∈ ambientFixedAddSubgroup (galoisAmbientUnitsRep K Ω)
    (closedFixingSubgroup K Ω E) ↔
  ((Additive.toMul x : Ωˣ) : Ω) ∈ E
```

Here `galoisAmbientUnitsRep K Ω` is the published abbreviation for Mathlib's
`Rep.ofAlgebraAutOnUnits K Ω`, the action of `Gal(Ω/K)` on `Additive Ωˣ`;
`closedFixingSubgroup K Ω E` is the published closed subgroup with
underlying subgroup `E.fixingSubgroup`; and
`ambientFixedAddSubgroup A H` is the published additive subgroup with carrier
`{a | ∀ h : H.toSubgroup, A.ρ h.1 a = a}`. The statement therefore says that
an ambient unit is fixed by every automorphism of `Ω` fixing `E` exactly when
its underlying field element lies in `E`.

## Implemented proof

The proof begins with

```lean
  change
    (∀ h : (closedFixingSubgroup K Ω E).toSubgroup,
        (galoisAmbientUnitsRep K Ω).ρ h.1 x = x) ↔
      ((Additive.toMul x : Ωˣ) : Ω) ∈ E
```

which unfolds the published proposition and membership in
`ambientFixedAddSubgroup` to the invariance condition. This is a definitional
change. It replaces the source's lines 65–70, a `change` to the same
membership with the element written as `show galoisAmbientUnitsRep K Ω from x`
followed by `rw [mem_ambientFixedAddSubgroup_iff]`. That source lemma,
`KummerTheory.mem_ambientFixedAddSubgroup_iff` (M023.002), is not published;
its source proof is `Iff.rfl`
(`Nyll/GaloisCohomology/Kummer/Abstract/KummerDelta.lean`, lines 49–53), so
the single `change` has the same effect. The remainder of the proof is the
original proof verbatim.

Forward direction: given the invariance `hx`, the goal is rewritten by
`InfiniteGalois.fixedField_fixingSubgroup E`, the infinite Galois
correspondence `IntermediateField.fixedField E.fixingSubgroup = E` (which uses
`[IsGalois K Ω]`), and then by `IntermediateField.mem_fixedField_iff`, leaving:
for each `σ ∈ E.fixingSubgroup`, `σ` fixes the field element of `x`. The
proof shows `σ ∈ (closedFixingSubgroup K Ω E).toSubgroup` by
`simpa only [closedFixingSubgroup]`, applies `hx` to it, and rewrites the
action by the definitional equation (`rfl`)

```lean
(Rep.ofAlgebraAutOnUnits K Ω).ρ σ x =
  Additive.ofMul (Units.mapEquiv σ.toMulEquiv (Additive.toMul x))
```

It takes the underlying field element of both sides with `congrArg` and closes
the goal by `convert hval using 1` followed by `rfl`.

Reverse direction: given that the field element of `x` lies in `E` and an
element `σ` of the closed fixing subgroup, the proof obtains
`σ.1 ∈ E.fixingSubgroup` by `simpa only [closedFixingSubgroup] using σ.2`,
rewrites the action by the same definitional equation, reduces the goal by
`Additive.ext`, `toMul_ofMul` and `Units.ext` to equality of field elements,
and closes it with
`convert (IntermediateField.mem_fixingSubgroup_iff E σ.1).1 hσE _ hx using 1`
followed by `rfl`.

No auxiliary declaration, extra hypothesis, instance or `simp` registration is
introduced. The development check reports only the standard axioms
`propext`, `Classical.choice` and `Quot.sound`.

## Actual dependencies

- The published proposition
  `Langlands.NYLL.LocalClassFieldTheory.mem_galoisAmbientUnits_fixed_iffStatement`
  in FixedUnits.Statements (unfolded by `change`).
- The published definitions
  `Langlands.NYLL.LocalClassFieldTheory.galoisAmbientUnitsRep`
  (AbsoluteUnitsFixedField.Initial.Definitions),
  `Langlands.NYLL.RamificationTheory.closedFixingSubgroup`
  (ValuedFieldTheory.Ramification.GaloisValuation.ClosedFixingSubgroup.Definitions)
  and `Langlands.NYLL.KummerTheory.ambientFixedAddSubgroup`
  (GaloisCohomology.Kummer.Abstract.KummerDelta.U001.Definitions), reached
  through the unchanged Statements import chain.
- Mathlib's `InfiniteGalois.fixedField_fixingSubgroup`
  (`Mathlib/FieldTheory/Galois/Infinite.lean`),
  `IntermediateField.mem_fixedField_iff`,
  `IntermediateField.mem_fixingSubgroup_iff`, `Rep.ofAlgebraAutOnUnits`,
  `Units.mapEquiv`, `Additive.ext`, `toMul_ofMul` and `Units.ext`, all available
  through the Statements module's imports.

The unpublished `KummerTheory.mem_ambientFixedAddSubgroup_iff` is not used and
no private copy of it is made. No other proof and no host class-formation or
reciprocity theorem is used.

## Pinned source and declaration map

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/AbsoluteUnitsFixedField.lean:57–105`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/AbsoluteUnitsFixedField.lean#L57-L105).
Lines 57–58 are the retained docstring, 59–64 the signature, 65–70 the
replaced opening `change` and rewrite, 71–89 the forward direction and 90–105
the reverse direction. The section variables are
`(K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]` at line 33 and
`[IsGalois K Ω]` at line 55. The
[public partition](../../../../../../../../../notes/reuse/nyll-public-port/m073-m096.md#m088)
places this proof at M088.004 (source unit lines 59–108) after M088.003.END.
The whole-file SHA-256 is
`392d08ca1431117423181ba326721905cc060686d340ba471b6838f85dd3ebfc`,
recomputed by Worker 96 on 13 November 2026 UTC from the retained snapshot.

| Original in `LocalClassFieldTheory` | Adapted in `Langlands.NYLL.LocalClassFieldTheory` |
| --- | --- |
| Asserted type of `mem_galoisAmbientUnits_fixed_iff` (M088.004) | Published `mem_galoisAmbientUnits_fixed_iffStatement` in FixedUnits.Statements |
| Proof `mem_galoisAmbientUnits_fixed_iff` | This theorem of the same adapted name in FixedUnits.U004.Proofs |
| `galoisAmbientUnitsRep` (M088.001) | Existing published abbreviation in AbsoluteUnitsFixedField.Initial.Definitions |
| `RamificationTheory.closedFixingSubgroup` | Existing published `Langlands.NYLL.RamificationTheory.closedFixingSubgroup` |
| `KummerTheory.ambientFixedAddSubgroup` | Existing published `Langlands.NYLL.KummerTheory.ambientFixedAddSubgroup` |
| `KummerTheory.mem_ambientFixedAddSubgroup_iff` (M023.002, `Iff.rfl`) | Not used; replaced by a definitional `change` |

The adaptation prefixes the namespace with `Langlands.NYLL`, replaces the
original imports by the sole published FixedUnits.Statements import, opens
only `RamificationTheory` and `KummerTheory` (the source also opens
`CyclicCohomology` and a `noncomputable section`, unused here), states the
theorem's type as the published proposition applied to `K Ω E x`, and
replaces the opening `change` and rewrite as described above.

The retained sources are registered as
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

This proof covers only M088.004. The evaluation lemma M088.003, the range
identification M088.005 and any host class-formation, cup, transfer, Tate or
reciprocity target are separate work.

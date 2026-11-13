# NYLL M088.005: range of the intermediate-field unit inclusion

This module proves the published Library proposition
`Langlands.NYLL.LocalClassFieldTheory.intermediateFieldUnitsToGaloisAmbient_rangeStatement`
by the theorem
`Langlands.NYLL.LocalClassFieldTheory.intermediateFieldUnitsToGaloisAmbient_range`.
The theorem's type is exactly that proposition applied to its source
parameters, `intermediateFieldUnitsToGaloisAmbient_rangeStatement K Ω E`.

Its direct imports are the published statement module
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbsoluteUnitsFixedField.FixedUnits.Statements`
and the published proof modules
`...AbsoluteUnitsFixedField.FixedUnits.U003.Proofs` (M088.003) and
`...AbsoluteUnitsFixedField.FixedUnits.U004.Proofs` (M088.004). These
published files and their complete imported chains remain unchanged.

## Target and parameters

The theorem has, in this order, explicit `K Ω : Type`, the instances
`[Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]` and an explicit
intermediate field `E : IntermediateField K Ω`. The extension `Ω/K` may be
infinite. No finite-dimensional, perfectness or local-field hypothesis is
assumed.

Unfolding the published proposition gives

```lean
(intermediateFieldUnitsToGaloisAmbient K Ω E).range =
  ambientFixedAddSubgroup (galoisAmbientUnitsRep K Ω)
    (closedFixingSubgroup K Ω E)
```

The left side is the range of the published additive inclusion
`Additive Eˣ →+ Additive Ωˣ`, `MonoidHom.toAdditive (Units.map E.val.toRingHom)`.
The right side is the published subgroup of ambient units `x` with
`(galoisAmbientUnitsRep K Ω).ρ h x = x` for every `h` in the closed fixing
subgroup of `E`, whose underlying subgroup is `E.fixingSubgroup`. The
statement says that the image of `Eˣ` in `Ωˣ` is exactly the subgroup of
ambient units fixed by `Gal(Ω/E)`.

## Implemented proof

The proof applies `AddSubgroup.ext` (directly to the stated type), fixes
`x : Additive Ωˣ` and proves both directions of membership.

Range into fixed subgroup: for `x` of the form
`intermediateFieldUnitsToGaloisAmbient K Ω E y`, a definitional `change`
writes the goal as membership of that element, viewed in the representation
space `galoisAmbientUnitsRep K Ω`, in the fixed subgroup. The reverse
direction of the published M088.004 theorem
`mem_galoisAmbientUnits_fixed_iff K Ω E _` reduces it to membership of the
underlying field element in `E`. Rewriting by `← ofMul_toMul y`, the
published M088.003 theorem `intermediateFieldUnitsToGaloisAmbient_apply`,
`toMul_ofMul` and `Units.coe_map` turns that element into the image of
`(Additive.toMul y : Eˣ).1 : E` in `Ω`, and its membership in `E` is the
`property` of that element.

Fixed subgroup into range: given `hx`, the forward direction of
`mem_galoisAmbientUnits_fixed_iff K Ω E x` gives `hxE`, that the field
element of `x` lies in `E`. Let `y₀ : E` be that element with proof `hxE`.
It is nonzero, since `E.val y₀ = 0` would make the unit `Additive.toMul x`
zero, contradicting `Units.ne_zero`. With `y := Units.mk0 y₀ hy₀ : Eˣ`, the
witness is `Additive.ofMul y`. The equation
`intermediateFieldUnitsToGaloisAmbient K Ω E (Additive.ofMul y) = x` is
proved by rewriting with `intermediateFieldUnitsToGaloisAmbient_apply`, then
`Additive.ext`, `toMul_ofMul`, `Units.ext` and `Units.coe_map`, and closing by
`rfl`.

Apart from stating the type as the published proposition, this is the
original proof verbatim; it rewrites with and applies the published M088.003
and M088.004 theorems under their adapted names. No auxiliary declaration,
extra hypothesis, instance or `simp` registration is introduced. The
development check reports only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Actual dependencies

- The published proposition
  `Langlands.NYLL.LocalClassFieldTheory.intermediateFieldUnitsToGaloisAmbient_rangeStatement`
  in FixedUnits.Statements.
- The published theorems
  `Langlands.NYLL.LocalClassFieldTheory.intermediateFieldUnitsToGaloisAmbient_apply`
  (M088.003, FixedUnits.U003.Proofs) and
  `Langlands.NYLL.LocalClassFieldTheory.mem_galoisAmbientUnits_fixed_iff`
  (M088.004, FixedUnits.U004.Proofs).
- The published definitions `intermediateFieldUnitsToGaloisAmbient`,
  `galoisAmbientUnitsRep` (AbsoluteUnitsFixedField.Initial.Definitions),
  `Langlands.NYLL.RamificationTheory.closedFixingSubgroup` and
  `Langlands.NYLL.KummerTheory.ambientFixedAddSubgroup`, reached through the
  unchanged Statements import chain.
- Mathlib's `AddSubgroup.ext`, `ofMul_toMul`, `toMul_ofMul`, `Units.coe_map`,
  `Units.ne_zero`, `Units.mk0`, `Additive.ext` and `Units.ext`.

The unpublished `KummerTheory.mem_ambientFixedAddSubgroup_iff` (M023.002) is
not used. No host class-formation or reciprocity theorem is used.

## Pinned source and declaration map

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/AbsoluteUnitsFixedField.lean:107–146`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/AbsoluteUnitsFixedField.lean#L107-L146).
Lines 107–108 are the retained docstring, 109–113 the signature, 114–126 the
range-into-fixed direction (with the `change` at 118–122) and 127–146 the
fixed-into-range direction. The section variables are
`(K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]` at line 33 and
`[IsGalois K Ω]` at line 55. The
[public partition](../../../../../../../../../notes/reuse/nyll-public-port/m073-m096.md#m088)
places this proof at M088.005 (source unit lines 109–149) after
M088.004.END. The whole-file SHA-256 is
`392d08ca1431117423181ba326721905cc060686d340ba471b6838f85dd3ebfc`,
recomputed by Worker 96 on 13 November 2026 UTC from the retained snapshot.

| Original in `LocalClassFieldTheory` | Adapted in `Langlands.NYLL.LocalClassFieldTheory` |
| --- | --- |
| Asserted type of `intermediateFieldUnitsToGaloisAmbient_range` (M088.005) | Published `intermediateFieldUnitsToGaloisAmbient_rangeStatement` in FixedUnits.Statements |
| Proof `intermediateFieldUnitsToGaloisAmbient_range` | This theorem of the same adapted name in FixedUnits.U005.Proofs |
| `intermediateFieldUnitsToGaloisAmbient_apply` (M088.003) | Published theorem in FixedUnits.U003.Proofs |
| `mem_galoisAmbientUnits_fixed_iff` (M088.004) | Published theorem in FixedUnits.U004.Proofs |

The adaptation prefixes the namespace with `Langlands.NYLL`, replaces the
original imports by the published Statements, U003.Proofs and U004.Proofs
imports, opens only `RamificationTheory` and `KummerTheory` (the source also
opens `CyclicCohomology` and a `noncomputable section`, unused here), and
states the theorem's type as the published proposition applied to `K Ω E`.

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

This proof covers only M088.005. The equivalence
`intermediateFieldUnitsEquivGaloisFixed` (M088.006) and later M088 units, and
any host class-formation, cup, transfer, Tate or reciprocity target, are
separate work.

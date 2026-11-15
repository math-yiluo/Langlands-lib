# NYLL M088.007: coercion law for the intermediate-field fixed-unit equivalence

This module proves the published Library proposition
`Langlands.NYLL.LocalClassFieldTheory.intermediateFieldUnitsEquivGaloisFixed_coeStatement`
by the theorem
`Langlands.NYLL.LocalClassFieldTheory.intermediateFieldUnitsEquivGaloisFixed_coe`.
The theorem's type is exactly that proposition applied to its source
parameters, `intermediateFieldUnitsEquivGaloisFixed_coeStatement K Ω E x`.

Its sole direct import is
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbsoluteUnitsFixedField.FixedUnitsEquiv.Statements`.
That published Lean/Markdown pair and its complete imported chain remain
unchanged.

## Target and parameters

The theorem is stated in the source's section telescope. Its parameters are,
in this order, explicit `K Ω : Type`, the instances
`[Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]`, an explicit intermediate
field `E : IntermediateField K Ω` and an explicit element
`x : Additive Eˣ`, exactly as in the published proposition.

Unfolding the published proposition gives

```lean
(intermediateFieldUnitsEquivGaloisFixed K Ω E x).1 =
  intermediateFieldUnitsToGaloisAmbient K Ω E x
```

Here `intermediateFieldUnitsToGaloisAmbient K Ω E` is the published additive
homomorphism `Additive Eˣ →+ Additive Ωˣ` induced by the inclusion `E → Ω`
(`MonoidHom.toAdditive (Units.map E.val.toRingHom)`), and
`intermediateFieldUnitsEquivGaloisFixed K Ω E` is the published additive
equivalence from `Additive Eˣ` onto the subgroup of `Additive Ωˣ` fixed by the
closed fixing subgroup `closedFixingSubgroup K Ω E` under the Galois
representation `galoisAmbientUnitsRep K Ω`. The statement says that the
underlying ambient unit (`.1`, the value in `Additive Ωˣ`) of the image of `x`
under the equivalence is just the image of `x` under the inclusion.

## Implemented proof

The complete proof term is

```lean
  rfl
```

The published equivalence is defined as `eRange.trans
(AddEquiv.addSubgroupCongr h)`, where
`eRange := AddMonoidHom.ofInjective _` is Mathlib's equivalence of
`Additive Eˣ` onto the range of the injective homomorphism
`intermediateFieldUnitsToGaloisAmbient K Ω E`, and `h` is the published range
equality `intermediateFieldUnitsToGaloisAmbient_range` (M088.005). The map
`AddMonoidHom.ofInjective` sends `x` to the range element
`⟨intermediateFieldUnitsToGaloisAmbient K Ω E x, _⟩`, and
`AddEquiv.addSubgroupCongr` does not change the underlying element. Hence both
sides of the equation agree after unfolding these definitions, and the kernel
accepts `rfl`. The published proposition is a definition that unfolds to this
equation, so `rfl` checks against the stated type directly.

Apart from stating the type as the published proposition, this is the
original proof verbatim. No auxiliary declaration, extra hypothesis, instance
or `simp` registration is introduced; in particular the source's `@[simp]`
attribute is not retained, because a theorem whose stated type is the
proposition definition is not a usable `simp` lemma. The development check
reports only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Actual dependencies

- The published proposition
  `Langlands.NYLL.LocalClassFieldTheory.intermediateFieldUnitsEquivGaloisFixed_coeStatement`
  in AbsoluteUnitsFixedField.FixedUnitsEquiv.Statements.
- The published definition
  `Langlands.NYLL.LocalClassFieldTheory.intermediateFieldUnitsEquivGaloisFixed`
  (AbsoluteUnitsFixedField.FixedUnitsEquiv.Definitions, M088.006), unfolded
  by the kernel, together with what its body uses: the published
  `intermediateFieldUnitsToGaloisAmbient` and `galoisAmbientUnitsRep`
  (AbsoluteUnitsFixedField.Initial.Definitions, M088.002 and M088.001), the
  published range theorem `intermediateFieldUnitsToGaloisAmbient_range`
  (AbsoluteUnitsFixedField.FixedUnits.U005.Proofs, M088.005, a proof argument
  only), `Langlands.NYLL.KummerTheory.ambientFixedAddSubgroup` and
  `Langlands.NYLL.RamificationTheory.closedFixingSubgroup`, all reached through
  the unchanged Statements import chain.
- Mathlib's `AddMonoidHom.ofInjective` and `AddEquiv.addSubgroupCongr`, through
  the same chain.

No other proof and no host class-formation or reciprocity theorem is used.

## Pinned source and declaration map

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/AbsoluteUnitsFixedField.lean:164–170`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/AbsoluteUnitsFixedField.lean#L164-L170).
Line 164 is the source docstring, 165 the `@[simp]` attribute, 166–169 the
signature and 170 the proof `rfl`; the
[public partition](../../../../../../../../../notes/reuse/nyll-public-port/m073-m096.md#m088)
places this proof at M088.007 (source unit lines 166–175, line 171 blank and
172–175 the docstring of the next declaration) after M088.006.END. The section
variables are `(K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]` at line 33 and
`[IsGalois K Ω]` at line 55. The whole-file SHA-256 is
`392d08ca1431117423181ba326721905cc060686d340ba471b6838f85dd3ebfc`,
recomputed by Worker 96 on 15 November 2026 UTC from the retained snapshot.

| Original in `LocalClassFieldTheory` | Adapted in `Langlands.NYLL.LocalClassFieldTheory` |
| --- | --- |
| Asserted type of `intermediateFieldUnitsEquivGaloisFixed_coe` (M088.007) | Published `intermediateFieldUnitsEquivGaloisFixed_coeStatement` in AbsoluteUnitsFixedField.FixedUnitsEquiv.Statements |
| Proof `intermediateFieldUnitsEquivGaloisFixed_coe` | This theorem of the same adapted name in AbsoluteUnitsFixedField.FixedUnitsEquiv.U007.Proofs |
| `intermediateFieldUnitsEquivGaloisFixed` (M088.006) | Existing published declaration of the same adapted name |
| `intermediateFieldUnitsToGaloisAmbient` (M088.002) | Existing published declaration of the same adapted name |

The adaptation prefixes the namespace with `Langlands.NYLL`, replaces the
original imports by the sole published Statements import, keeps the source
section variables, omits the source openings
`RamificationTheory KummerTheory CyclicCohomology` and the
`noncomputable section` (unused by the proof term), drops the `@[simp]`
attribute and states the theorem's type as the published proposition applied
to `K Ω E x`.

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

This proof covers only M088.007. The base-unit value law M096.002, the coset
action law M096.004 and any host class-formation, cup, transfer, Tate or
reciprocity target are separate work.

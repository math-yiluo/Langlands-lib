# Intrinsic-to-ambient embedded base equivalence: application statements

This module defines two closed propositions in
`Langlands.NYLL.LocalClassFieldTheory`, the statement phases of source rows
M273.007 and M273.008:

- `intrinsicBaseEquivAmbientEmbeddedField_applyStatement`, for the source
  theorem `intrinsicBaseEquivAmbientEmbeddedField_apply`;
- `intrinsicBaseEquivAmbientEmbeddedField_apply_valStatement`, for the source
  theorem `intrinsicBaseEquivAmbientEmbeddedField_apply_val`.

Each is a `def` returning `Prop` that packages the complete source theorem
signature. Neither has a proof here. Later proof children will prove them
under the names
`Langlands.NYLL.LocalClassFieldTheory.intrinsicBaseEquivAmbientEmbeddedField_apply`
and
`Langlands.NYLL.LocalClassFieldTheory.intrinsicBaseEquivAmbientEmbeddedField_apply_val`.

Both describe the published multiplicative equivalence
`intrinsicBaseEquivAmbientEmbeddedField K F i e` (source row M273.006, module
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.BaseComparison.IntrinsicBaseEquivalence.U004.Definitions`)
from the intrinsic base subgroup of `F` onto the closed subgroup of
`Gal(SeparableClosure K / K)` fixing `i(F)`.

## Common parameters and local data

Both propositions universally quantify, in the source order,

```lean
(K F : Type) [Field K] [Field F]
  [Algebra K F] [FiniteDimensional K F] [Algebra.IsSeparable K F]
  (i : F →ₐ[K] SeparableClosure K)
```

So `F / K` is a finite separable extension of fields in `Type` (universe zero,
as in the source), and `i` is a `K`-algebra embedding of `F` into Mathlib's
separable closure `SeparableClosure K`. There is no valuation, topology or
local-field hypothesis. Both then introduce, as in the source,

```lean
letI : Algebra F (SeparableClosure F) :=
  (separableClosure F (AlgebraicClosure F)).algebra
letI : Algebra F (SeparableClosure K) := i.toRingHom.toAlgebra
```

The first local instance is the algebra structure of the intermediate field
`separableClosure F (AlgebraicClosure F)`, which is how Mathlib defines
`SeparableClosure F`. The second makes `SeparableClosure K` an `F`-algebra
through `i`. Both propositions then quantify over an `F`-algebra isomorphism
`e : SeparableClosure F ≃ₐ[F] SeparableClosure K` for these structures and an
element `tau` of `(intrinsicAbstractBase F).toSubgroup`. The Library
`intrinsicAbstractBase F` is the closed subgroup of `Gal(SeparableClosure F / F)`
fixing the bottom intermediate field, which is the whole group.

## The proposition `intrinsicBaseEquivAmbientEmbeddedField_applyStatement`

After `e` and `tau`, the proposition introduces the following local data,
verbatim from the source:

- `H₀ := closedFixingSubgroup K (SeparableClosure K) (AlgHom.fieldRange i)`,
  the closed subgroup of `Gal(SeparableClosure K / K)` fixing `i(F)`;
- a local instance `hHabsolute` that the quotient of
  `(baseField Gal(SeparableClosure K / K)).toSubgroup` by
  `extensionSubgroup (baseField _) H₀ (le_baseField H₀)` is finite, proved by
  the published theorem `ambientEmbeddedAbsoluteQuotientFinite K F i`
  (source row M273.001);
- `_H : FiniteAbstractField Gal(SeparableClosure K / K) := ⟨H₀, hHabsolute⟩`,
  which the conclusion does not use (the source names it `_H`);
- `F₀ := abstractFixedField K (SeparableClosure K) H₀`, the fixed field of
  `H₀`, an intermediate field of `SeparableClosure K / K`;
- `hfixed : F₀ = AlgHom.fieldRange i`, the Mathlib Galois-correspondence
  identity `InfiniteGalois.fixedField_fixingSubgroup (AlgHom.fieldRange i)`;
- `phi : F ≃+* F₀`, the ring isomorphism `i.equivFieldRange` followed by
  `IntermediateField.equivOfEq hfixed.symm`;
- `rho : Gal(SeparableClosure K / F₀)`, the ring automorphism
  `x ↦ e (tau.1 (e.symm x))` of `SeparableClosure K`, with the source's
  tactic proof that it fixes `F₀` pointwise. That proof uses
  `e.commutes`, `tau.1.commutes` and the fact that the coercion of
  `phi y` to `SeparableClosure K` is `i y`.

The conclusion is

```lean
intrinsicBaseEquivAmbientEmbeddedField K F i e tau =
  (abstractSubgroupEquivGaloisGroup K (SeparableClosure K) H₀).symm rho
```

So the image of `tau` is the element of `H₀` that the Library equivalence
`abstractSubgroupEquivGaloisGroup` (source row M099.007,
`H₀.toSubgroup ≃* Gal(SeparableClosure K / F₀)`) matches with the conjugate
`rho = e ∘ tau ∘ e⁻¹`.

## The proposition `intrinsicBaseEquivAmbientEmbeddedField_apply_valStatement`

After `e` and `tau` it also quantifies over `x : SeparableClosure K` and
concludes

```lean
(intrinsicBaseEquivAmbientEmbeddedField K F i e tau).1.1 x =
  e (tau.1 (e.symm x))
```

Here `.1` takes the underlying element of `Gal(SeparableClosure K / K)` from
the subgroup element and then its underlying `Equiv`, which is applied to `x`.
So the image of `tau` acts on `SeparableClosure K` as `e ∘ tau ∘ e⁻¹`. This
proposition uses none of the local data of the first one.

## Reused Library declarations

| Source unit and original declaration | Library declaration used |
| --- | --- |
| M273.006, `LocalClassFieldTheory.intrinsicBaseEquivAmbientEmbeddedField` | `Langlands.NYLL.LocalClassFieldTheory.intrinsicBaseEquivAmbientEmbeddedField` (module `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.BaseComparison.IntrinsicBaseEquivalence.U004.Definitions`) |
| M273.001, `LocalClassFieldTheory.ambientEmbeddedAbsoluteQuotientFinite` | `Langlands.NYLL.LocalClassFieldTheory.ambientEmbeddedAbsoluteQuotientFinite` (module `...IntrinsicBaseEquivalence.U001.Proofs`, imported through the U004 module) |
| M091.003, `LocalClassFieldTheory.intrinsicAbstractBase` | `Langlands.NYLL.LocalClassFieldTheory.intrinsicAbstractBase` (module `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData.Initial.Definitions`) |
| M087.001, `RamificationTheory.closedFixingSubgroup` | `Langlands.NYLL.RamificationTheory.closedFixingSubgroup` (module `Langlands.NYLL.ValuedFieldTheory.Ramification.GaloisValuation.ClosedFixingSubgroup.Definitions`) |
| M010.003, `ClassFormation.baseField` | `Langlands.NYLL.ClassFormation.baseField` (module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Definitions`) |
| M010.005, `ClassFormation.le_baseField` | `Langlands.NYLL.ClassFormation.le_baseField` (module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.U005.Proofs`) |
| M004.002, `CyclicCohomology.extensionSubgroup` | `Langlands.NYLL.CyclicCohomology.extensionSubgroup` (module `Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions`) |
| M010.121, `ClassFormation.FiniteAbstractField` | `Langlands.NYLL.ClassFormation.FiniteAbstractField` (module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.Definitions`) |
| M099.001, `LocalClassFieldTheory.abstractFixedField` | `Langlands.NYLL.LocalClassFieldTheory.abstractFixedField` (module `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteAbstractFixedField.Initial.Definitions`) |
| M099.007, `LocalClassFieldTheory.abstractSubgroupEquivGaloisGroup` | `Langlands.NYLL.LocalClassFieldTheory.abstractSubgroupEquivGaloisGroup` (same module) |

All of these declarations are published in the Library and are used under the
names above, reached through the source's `open RamificationTheory
CyclicCohomology` and `open ClassFormation` lines inside the namespace
`Langlands.NYLL.LocalClassFieldTheory`. The statements are otherwise the
source text.

## Relation to other Library and Mathlib declarations

No published declaration states either proposition: the equivalence they
describe exists only in this port. Mathlib's `AlgEquiv.autCongr` performs the
same conjugation `tau ↦ e ∘ tau ∘ e⁻¹` between automorphism groups, and
`IntermediateField.fixingSubgroupEquiv` identifies a fixing subgroup with a
relative Galois group; the first proposition expresses
`intrinsicBaseEquivAmbientEmbeddedField` through such a conjugate. The
Library module `Langlands/ClassFieldTheory/Local/ClosureRestrictionTransport.lean`
(namespace `Langlands.ClassFieldTheory.Local`: `closureSubgroupMulEquiv`,
`closureSubgroupEquiv_apply_val`) identifies the
absolute Galois group of an intermediate field `E` of an algebraic closure
with `E.fixingSubgroup` by a different construction, for intermediate fields
of an algebraic closure (its topological version assumes characteristic
zero); it does not state either proposition.

## Original source

The original source is Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/BaseComparison/IntrinsicBaseEquivalence.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/BaseComparison/IntrinsicBaseEquivalence.lean>).
The complete file was read and its SHA-256 verified as
`0c4403626ce06952a02d1bd927112542e4f69466ca939a1d0896195d94ef5800`.
The M273.007 docstring occupies lines 309–311 and its signature lines
312–374; its proof occupies lines 375–496. The M273.008 docstring occupies
lines 498–499 and its signature lines 500–514; its proof occupies lines
515–584. The header occupies lines 1–5, the `noncomputable section` line 20,
the namespace line 22 and the `open` lines 24–26.

| Source unit and original declaration | Adapted declaration and phase |
| --- | --- |
| M273.007, `LocalClassFieldTheory.intrinsicBaseEquivAmbientEmbeddedField_apply` | `Langlands.NYLL.LocalClassFieldTheory.intrinsicBaseEquivAmbientEmbeddedField_applyStatement`, closed Prop target |
| M273.008, `LocalClassFieldTheory.intrinsicBaseEquivAmbientEmbeddedField_apply_val` | `Langlands.NYLL.LocalClassFieldTheory.intrinsicBaseEquivAmbientEmbeddedField_apply_valStatement`, closed Prop target |
| Same source theorems, later proof phase | `Langlands.NYLL.LocalClassFieldTheory.intrinsicBaseEquivAmbientEmbeddedField_apply` and `Langlands.NYLL.LocalClassFieldTheory.intrinsicBaseEquivAmbientEmbeddedField_apply_val`, reserved for the proof children |

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
with supplement `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Modifications and attribution

Worker 57 made these changes to the two source theorems:

- Each theorem becomes a Prop-valued definition with the `Statement`
  suffix. Its explicit parameters become universal binders in the same
  order, and the proof is omitted for the separate proof phase. The
  binders, local `let`/`letI` data and conclusions are otherwise the source
  text, including the tactic proofs inside `hHabsolute` and `rho`.
- The namespace `LocalClassFieldTheory` is prefixed with `Langlands.NYLL`.
- The source imports are replaced by the Library module that publishes
  `intrinsicBaseEquivAmbientEmbeddedField` (which imports the other Library
  declarations used, except `extensionSubgroup`) and the Library module that
  publishes `extensionSubgroup`.
- The `noncomputable section` and the unused `open LocalFieldTheory` and
  `KummerTheory` are omitted. All other declarations of the source file are
  omitted.

The Lean header keeps the original 2026 Naganori Yamaguchi copyright,
the authorship line including OpenAI Codex assistance, and the Apache-2.0
notice. It also records these modifications. The existing
[LICENSE](../../../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../../../licenses/NYLL/NOTICE) match the pinned
upstream files. Their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

This unit contains only the M273.007 and M273.008 statement targets. Their
proofs and the other rows of the source file are not part of this unit.

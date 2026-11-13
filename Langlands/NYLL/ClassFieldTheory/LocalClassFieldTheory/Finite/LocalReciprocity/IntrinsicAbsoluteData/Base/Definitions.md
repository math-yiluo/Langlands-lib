# The intrinsic abstract base as a finite abstract field

Adapted by Worker 57 from Naganori Yamaguchi, ClassFieldTheory, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/IntrinsicAbsoluteData.lean`
(file SHA-256 `307ae64486245113f5aa94505bbc184048f4daec1af85f89f94f965c57b25e5a`).
Registered source: `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. The source file is readable under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.

| Unit | Original declaration and source lines | Adapted declaration |
| --- | --- | --- |
| M091.006 | `intrinsicFiniteAbstractBase` (66–75) | `intrinsicFiniteAbstractBase` |

The original name is in `LocalClassFieldTheory`; the adapted name is
`Langlands.NYLL.LocalClassFieldTheory.intrinsicFiniteAbstractBase`.

This unit is listed in Task 6255 (a child of Task 5264), which names the
directory `IntrinsicAbsoluteData/Base/`. Worker 5264, who routes that task,
asked Worker 57 to stage it under Task 5799 so that Task 6255 can discharge
it by Lean name.

## Content

For a field `F : Type`, `intrinsicFiniteAbstractBase F` is a term of
`FiniteAbstractField (intrinsicAbsoluteGalois F)`. `intrinsicAbsoluteGalois F`
is `Gal(SeparableClosure F / F)`. A `FiniteAbstractField G` is a closed subgroup
`field` of `G` together with a proof `finite` that the quotient of the
distinguished base field `baseField G` (the closed subgroup whose underlying
subgroup is `⊤`) by the
extension subgroup of `field` is finite.

- The field `field` is `intrinsicAbstractBase F`: the closed fixing subgroup
  of the bottom intermediate field `⊥` of `SeparableClosure F` over `F`.
- The field `finite` is proved by rewriting `intrinsicAbstractBase F` to
  `baseField (intrinsicAbsoluteGalois F)` and then using the finiteness proof
  stored in `FiniteAbstractField.base (intrinsicAbsoluteGalois F)`, whose
  quotient is trivial.

The definition is marked `@[reducible]` and `noncomputable`, as in the source.
Its `field` component is the term `intrinsicAbstractBase F`, not
`baseField (intrinsicAbsoluteGalois F)`. The two closed subgroups are equal, but
not by definition. The source theorem `intrinsicFiniteAbstractBase_eq_base`
(M091.007, lines 77–85) states the resulting equality
`intrinsicFiniteAbstractBase F = FiniteAbstractField.base (intrinsicAbsoluteGalois F)`.
It is a theorem and is not part of this unit.

Published components used, all by their Library names:

- `Langlands.NYLL.LocalClassFieldTheory.intrinsicAbsoluteGalois` (M091.001)
  and `intrinsicAbstractBase` (M091.003), from
  `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData.Initial.Definitions`;
- `Langlands.NYLL.LocalClassFieldTheory.closedFixingSubgroup_bot_eq_baseField`
  (M089.001), proved in
  `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GaloisExtensionQuotient.Initial.U001.Proofs`;
- `Langlands.NYLL.ClassFormation.FiniteAbstractField` (M010.121) and
  `Langlands.NYLL.ClassFormation.FiniteAbstractField.base` (M010.123), from
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.Definitions`.

## Modifications

- The source namespace `LocalClassFieldTheory` is prefixed by `Langlands.NYLL`.
  The definition is placed in its own file `IntrinsicAbsoluteData/Base/Definitions`,
  the directory named by Task 6255.
- The source imports `Mathlib.FieldTheory.IsSepClosed` and the broad module
  `GaloisExtensionQuotient`. The port imports only the three published modules
  listed above. The source opens
  `RamificationTheory CyclicCohomology KummerTheory ClassFormation`. The port
  opens `RamificationTheory` and `ClassFormation`. `CyclicCohomology` and
  `KummerTheory` are not used by this definition and are not opened.
- The docstring, the `@[reducible]` attribute, the `noncomputable` modifier,
  the explicit `Type`-zero field parameter `F` with `[Field F]`, the result
  type, the `field` value and the tactic proof of `finite` are copied from
  source lines 66–75 without change. The rewrite with
  `closedFixingSubgroup_bot_eq_baseField` uses the published theorem, which
  is stated through its Prop-valued target
  `closedFixingSubgroup_bot_eq_baseFieldStatement`. The rewrite goes through
  unchanged.
- No other declaration of the source module is included.

## Library and Mathlib comparison

No Library declaration bundles `intrinsicAbstractBase F` as a
`FiniteAbstractField`. A search of the Library `.lean` files (commit
`77763a3ff7dc9abc0457a63c7eda86d83f2b2274`) for `intrinsicAbstractBase` found it
only in its defining module, in the published `intrinsicAbstractBaseEquivAbsolute`
(M091.004, `IntrinsicAbsoluteData/U004/Definitions`), and in the abbreviation
`Langlands.NYLL.PortInternal.M097.d003`, which restates the closed subgroup and
does not package it. Terms of type `FiniteAbstractField _` are constructed only
in `FiniteAbstractField/Definitions` (`FiniteAbstractField.base`) and in the
generic structures of `FiniteAbstractField/Extension` and
`UnitCohomologyAxiom`. `FiniteAbstractField.base (intrinsicAbsoluteGalois F)`
is propositionally equal to this definition, as noted under Content. It is not
a definitional substitute, because its `field` is `baseField _` rather than
`intrinsicAbstractBase F`. Mathlib has no notion of `FiniteAbstractField`.

The original copyright and author header is retained. Apache-2.0 attribution
and notices are in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.

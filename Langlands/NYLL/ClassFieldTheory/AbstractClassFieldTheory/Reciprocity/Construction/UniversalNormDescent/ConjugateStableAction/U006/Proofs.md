# The conjugation-stable action after coercion

This module proves the theorem
`Langlands.NYLL.ClassFormation.conjugateStableAction_coe`, the proof phase of
M043.006 in the
[NYLL partition](../../../../../../../../../notes/reuse/nyll-public-port/m025-m048.md#m043).
Its type is the published proposition
`Langlands.NYLL.ClassFormation.conjugateStableAction_coeStatement` applied to the
theorem's parameters:

```lean
theorem conjugateStableAction_coe
    {R : IntegralRepGroupType} [Group R] [TopologicalSpace R] [ContinuousMul R]
    (B : Rep ℤ R) (F : ClosedSubgroup R) (s : R)
    (hF : conjugateClosedSubgroup F s = F)
    (a : ambientFixedAddSubgroup B F) :
    conjugateStableAction_coeStatement B F s hF a
```

## Target and binders

The theorem has its own binders `{R : IntegralRepGroupType} [Group R] [TopologicalSpace R] [ContinuousMul R]`, `B`, `F`, `s`, `hF` and `a`, exactly as the published target and the source theorem; the module declares no section variables or universes.

By its definition in the published module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.UniversalNormDescent.ConjugateStableAction.Statements`, the target is the proposition

```lean
((conjugateStableAction B F s hF a : ambientFixedAddSubgroup B F) : B.V) =
  B.ρ s⁻¹ a.1
```

Here `R` is a topological group with continuous multiplication (in the universe-zero type `IntegralRepGroupType`), `B : Rep ℤ R`, `F : ClosedSubgroup R` and `s : R` with `hF : conjugateClosedSubgroup F s = F` (M026.001: the conjugate field `F^s` is `F`), and `a : ambientFixedAddSubgroup B F` (M023.001, the elements of `B.V` fixed by `F`). `conjugateStableAction B F s hF a` (M043.003) is the right conjugate `conjugateFixedElement B F s a` (M026.003), fixed by `F^s`, transported along `hF` to an element fixed by `F`. The target says that its underlying element of `B.V` is `B.ρ s⁻¹ a.1`. No hypothesis is added.

## Imports and dependencies

The module imports, unchanged:

- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.UniversalNormDescent.ConjugateStableAction.Statements`, which defines the target and imports `conjugateStableAction` (M043.003), `conjugateFixedElement` (M026.003), `conjugateClosedSubgroup` (M026.001) and `ambientFixedAddSubgroup` (M023.001).

The module opens `KummerTheory`, as the source does, for `ambientFixedAddSubgroup`; the source's `open CyclicCohomology`, `open CategoryTheory` and `open scoped BigOperators` and its universes `u v` are not needed.

## Implemented proof

The module first proves the private source helper M043.004 `transport_fixed_coe` as a private theorem with its source statement and proof: for an equality `h : F' = F` of closed subgroups and `a` fixed by `F'`, the transport `h ▸ a` has the same underlying element `a.1`; `cases h` reduces it to `rfl`.

After `show` states the published proposition unfolded, the proof is the source proof `exact transport_fixed_coe B _ F hF _`: by its definition (M043.003), `conjugateStableAction B F s hF a` is `hF ▸ conjugateFixedElement B F s a`, so the helper identifies its underlying element with that of `conjugateFixedElement B F s a`, which is `B.ρ s⁻¹ a.1` by definition (M026.003).

The development check with `lean_check` in the approved environment compiled the
module with no errors or warnings. This check does not establish independent semantic
acceptance or Integrator publication.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709), commit `fbd320cd8b1b06487c58227e92eb135794267709`. The exact
passages are
[`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/UniversalNormDescent.lean`, lines 80–86](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/UniversalNormDescent.lean#L80-L86) and [`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/UniversalNormDescent.lean`, lines 104–113](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/UniversalNormDescent.lean#L104-L113):
the private helper `transport_fixed_coe` (M043.004) at lines 80–86, and the docstring at line 104, the attribute at line 105 and the theorem at lines 106–113. They lie in `namespace ClassFormation` (line 20), with `open KummerTheory` (line 22) and `open CyclicCohomology` (line 23), after `universe u v` (line 18), in its `noncomputable section` (line 27) with `open CategoryTheory` (line 29) and `open scoped BigOperators` (line 30). The source passages are:

```lean
private theorem transport_fixed_coe
    {R : IntegralRepGroupType} [Group R] [TopologicalSpace R]
    (B : Rep ℤ R) (F' F : ClosedSubgroup R) (h : F' = F)
    (a : ambientFixedAddSubgroup B F') :
    (((h ▸ a : ambientFixedAddSubgroup B F) : B.V)) = a.1 := by
  cases h
  rfl
```

```lean
/-- The conjugation-stable action agrees with its ambient action after coercion. -/
@[simp]
theorem conjugateStableAction_coe
    {R : IntegralRepGroupType} [Group R] [TopologicalSpace R] [ContinuousMul R]
    (B : Rep ℤ R) (F : ClosedSubgroup R) (s : R)
    (hF : conjugateClosedSubgroup F s = F)
    (a : ambientFixedAddSubgroup B F) :
    ((conjugateStableAction B F s hF a : ambientFixedAddSubgroup B F) : B.V) =
      B.ρ s⁻¹ a.1 := by
  exact transport_fixed_coe B _ F hF _
```

The complete original file is retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/UniversalNormDescent.lean`;
its SHA-256 is `5ac5450e039760193ab008f2bed81158a543d2d9982515cd2e376baeadfe1284`.

Modifications by Worker 5264 on 15 November 2026:

- add the `Langlands.NYLL` namespace prefix and replace the source imports by the Library imports listed above;
- port the private helper `transport_fixed_coe` (M043.004) as a private theorem of this module, with its source statement and proof;
- give the theorem the published proposition `conjugateStableAction_coeStatement B F s hF a` as its type, and begin the proof with `show` stating it unfolded;
- omit the `@[simp]` attribute (the theorem's type is the published `...Statement` proposition, not an equation), the universes `u v`, `open CyclicCohomology`, `open CategoryTheory`, `open scoped BigOperators` and all other source declarations.

The names, binders and proof steps of both theorems and the docstring of `conjugateStableAction_coe` are the source's; the helper has no docstring in the source or the port. The retained original belongs to registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`; additional
attribution material is registered as `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The approved environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`).

## Attribution and boundary

The original copyright and author header is preserved verbatim: copyright 2026
Naganori Yamaguchi, author “Naganori Yamaguchi (assisted by OpenAI Codex)”, released
under Apache-2.0. The Lean file carries the dated modification record. The unchanged
[LICENSE](../../../../../../../../../licenses/NYLL/LICENSE) (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
[NOTICE](../../../../../../../../../licenses/NYLL/NOTICE) (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`) are in the
Library. No Mathlib code is copied.

This module proves only M043.006. It discharges no host class-formation, cup,
transfer, Tate or reciprocity target.

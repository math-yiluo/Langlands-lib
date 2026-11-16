# The Frobenius exponent is positive

This module proves the theorem
`Langlands.NYLL.ClassFormation.DegreeData.frobeniusExponent_pos`, the proof phase of
M014.013 in the
[NYLL partition](../../../../../../../../notes/reuse/nyll-public-port/m001-m024.md#m014).
Its type is the published proposition
`Langlands.NYLL.ClassFormation.DegreeData.frobeniusExponent_posStatement` applied to the
theorem's parameters:

```lean
theorem frobeniusExponent_pos (D : DegreeData G) (K : FiniteResidueAbstractField D) (L :
  ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    frobeniusExponent_posStatement D K L hLK σ
```

## Target and binders

The theorem has the binders of the published target, in the same order: the section variables `{G : Type u} [Group G] [TopologicalSpace G]` (the ambient group with its group structure and topology, in the source universe `u`), then the explicit parameters `D : DegreeData G` (M010.002, the degree datum: a continuous surjective degree homomorphism `G → ℤ̂`), `K : FiniteResidueAbstractField D` (M010.021, an abstract field with finite residue degree), `L : ClosedSubgroup G` and `hLK : L.toSubgroup ≤ K.field.toSubgroup` (an abstract extension `L` of `K`), the instance argument `[hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]` (normality of `L` in `K`) and `σ : D.FrobeniusElements K L hLK` (a Frobenius lift, M012.009: a class `σ` in `G(\widetilde L|K) = K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK` together with the property that its normalized degree `D.extensionNormalizedDegree K L hLK σ` (M012.005) is `(Multiplicative.ofAdd (1 : ZHat)) ^ n` for some natural number `n > 0`). The source writes the subgroup in `hLnormal` as `extensionSubgroup K.field L hLK`, an abbreviation whose body is exactly `L.toSubgroup.subgroupOf K.field.toSubgroup`; the published target uses the body.

By its definition in the published module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField.FrobeniusClosure.Statements`, the target is the proposition

```lean
0 < D.frobeniusExponent K L hLK σ
```

That is, the Frobenius exponent `frobeniusExponent` (M014.012) of `σ`, the natural number `n` chosen from the defining property of `σ`, is positive. No hypothesis is added.

## Imports and dependencies

The module imports, unchanged:

- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField.FrobeniusClosure.Statements`, which defines the target and imports the published definitions `FrobeniusElements` (M012.009), `extensionNormalizedDegree` (M012.005) and `frobeniusExponent` (M014.012).

The module opens no namespace.

## Implemented proof

The proof unfolds the target with `show` to `0 < D.frobeniusExponent K L hLK σ` and closes it with `exact (Exists.choose_spec σ.2).1`. The property `σ.2` of the Frobenius lift states `∃ n : ℕ, 0 < n ∧ D.extensionNormalizedDegree K L hLK σ = (Multiplicative.ofAdd (1 : ZHat)) ^ n`, and `frobeniusExponent` (M014.012) is by definition `Exists.choose σ.2`. So `Exists.choose_spec σ.2` is this conjunction for the chosen exponent, and its first component is the positivity. This is the source proof term.

The development check with `lean_check` in the approved environment compiled the
module with no errors or warnings. This check does not establish independent semantic
acceptance or Integrator publication.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709), commit `fbd320cd8b1b06487c58227e92eb135794267709`. The exact
passage is
[`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/FrobeniusFixedField.lean`, lines 309–316](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/FrobeniusFixedField.lean#L309-L316):
the docstring at line 309 and the theorem at lines 310–316. It lies in `namespace ClassFormation` (line 19), with `open CyclicCohomology` (line 21), its `noncomputable section` (line 25), `universe u` (line 27), the group variables of line 29 and `namespace DegreeData` (line 300). The source is:

```lean
/-- The Frobenius exponent attached to a finite extension is strictly positive. -/
theorem frobeniusExponent_pos (D : DegreeData G) (K : FiniteResidueAbstractField D) (L :
  ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    0 < D.frobeniusExponent K L hLK σ :=
  (Exists.choose_spec σ.2).1
```

The complete original file is retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/FrobeniusFixedField.lean`;
its SHA-256 is `cda9dddf5f551fc8c81de825093b52cba99d644e45eb274682d2ee986585bfe3`.

Modifications by Worker 752 on 16 November 2026, adapting the draft by Worker 5264 of 15 November 2026:

- give the theorem the published proposition `frobeniusExponent_posStatement D K L hLK σ` as its type; the source term proof becomes a tactic proof that unfolds this type with an initial `show` and then gives the source term with `exact`;
- add the `Langlands.NYLL` namespace prefix and replace the source imports by the Library imports listed above;
- expand `extensionSubgroup K.field L hLK` to its abbreviation body `L.toSubgroup.subgroupOf K.field.toSubgroup`, as in the published target;
- omit `open CyclicCohomology` (only needed for the abbreviation), the `noncomputable section` and all other source declarations.

The theorem name, its binders, the source universe and variable declarations, its docstring and the proof term are kept. The retained original belongs to registered source
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
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`) are in the
Library. No Mathlib code is copied.

This module proves only M014.013. It discharges no host class-formation, cup,
transfer, Tate or reciprocity target.

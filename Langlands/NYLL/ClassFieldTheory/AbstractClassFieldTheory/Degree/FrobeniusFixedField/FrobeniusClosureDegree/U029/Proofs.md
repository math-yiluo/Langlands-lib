# The degree of the Frobenius-closure generator

This module proves the theorem
`Langlands.NYLL.ClassFormation.DegreeData.frobeniusClosureDegree_generator`, the proof phase of
M014.029 in the
[NYLL partition](../../../../../../../../notes/reuse/nyll-public-port/m001-m024.md#m014).
Its type is the published proposition
`Langlands.NYLL.ClassFormation.DegreeData.frobeniusClosureDegree_generatorStatement` applied to the
theorem's parameters:

```lean
theorem frobeniusClosureDegree_generator (D : DegreeData G)
    [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    frobeniusClosureDegree_generatorStatement D K L hLK σ
```

## Target and binders

The theorem has the binders of the published target, in the same order: the section variables `{G : Type u} [Group G] [TopologicalSpace G]`, then `D : DegreeData G` (M010.002), `[IsTopologicalGroup G]`, `K : FiniteResidueAbstractField D` (M010.021), a closed subgroup `L` with `hLK : L.toSubgroup ≤ K.field.toSubgroup`, the instance `hLnormal` that `G_L` is normal in `G_K`, and a Frobenius lift `σ : D.FrobeniusElements K L hLK` (M012.009). The source writes the normality instance with `extensionSubgroup K.field L hLK`, an abbreviation whose body is exactly `L.toSubgroup.subgroupOf K.field.toSubgroup`; the published target uses the body.

By its definition in the published module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField.FrobeniusClosureDegree.Statements`, the target is the proposition

```lean
D.frobeniusClosureDegree K L hLK σ
    (D.frobeniusInClosure K L hLK σ) =
  (Multiplicative.ofAdd (1 : ZHat)) ^
      D.frobeniusExponent K L hLK σ
```

That is, the normalized degree on the Frobenius closure `Γ`, `frobeniusClosureDegree` (M014.028), sends the chosen generator `frobeniusInClosure` (M014.024, the lift `σ` regarded in `Γ`) to the `n`-th power of the multiplicative generator `ofAdd 1` of `ℤ̂`, where `n = frobeniusExponent` (M014.012) is the exponent chosen for `σ`. No hypothesis is added.

## Imports and dependencies

The module imports, unchanged:

- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField.FrobeniusClosureDegree.Statements`, which defines the target and imports the published definitions `frobeniusClosureDegree` (M014.028), `frobeniusInClosure` (M014.024) and `frobeniusExponent` (M014.012).

The module opens no namespace.

## Implemented proof

As in the source, `change` rewrites the target as an equation for the normalized degree `extensionNormalizedDegree` (M012.005) of the underlying element of the generator, the local equation `hval`, proved by `rfl`, identifies that element with `σ.1`, and `rw [hval]` leaves the equation `D.extensionNormalizedDegree K L hLK σ.1 = (ofAdd 1) ^ n`. The source closes this goal with M014.014 `extensionNormalizedDegree_frobenius_eq_pow` (lines 319–327), whose proof is not in the Library; the module gives that theorem's one-line source proof `(Exists.choose_spec σ.2).2` instead. Here `σ.2` states that some positive `n` has `extensionNormalizedDegree K L hLK σ.1 = (ofAdd 1)^n`, and `frobeniusExponent` is defined as `Exists.choose σ.2` (lines 303–307), so the second component of `Exists.choose_spec σ.2` is exactly the goal.

The development check with `lean_check` in the approved environment compiled the
module with no errors or warnings. This check does not establish independent semantic
acceptance or Integrator publication.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709), commit `fbd320cd8b1b06487c58227e92eb135794267709`. The exact
passage is
[`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/FrobeniusFixedField.lean`, lines 566–585](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/FrobeniusFixedField.lean#L566-L585):
the docstring at line 566, the attribute at line 567 and the theorem at lines 568–585. It lies in `namespace ClassFormation` (line 19), with `open CyclicCohomology` (line 21), its `noncomputable section` (line 25), `universe u` (line 27), the variables `{G : Type u} [Group G] [TopologicalSpace G]` (line 29) and `namespace DegreeData` (line 300). The source is:

```lean
/-- The degree map sends the canonical Frobenius-closure generator to its expected value. -/
@[simp]
theorem frobeniusClosureDegree_generator (D : DegreeData G)
    [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    D.frobeniusClosureDegree K L hLK σ
        (D.frobeniusInClosure K L hLK σ) =
      (Multiplicative.ofAdd (1 : ZHat)) ^
          D.frobeniusExponent K L hLK σ := by
  change D.extensionNormalizedDegree K L hLK
      (D.frobeniusInClosure K L hLK σ).1 =
    (Multiplicative.ofAdd (1 : ZHat)) ^
      D.frobeniusExponent K L hLK σ
  have hval :
      (D.frobeniusInClosure K L hLK σ).1 = σ.1 := rfl
  rw [hval]
  exact D.extensionNormalizedDegree_frobenius_eq_pow K L hLK σ
```

The complete original file is retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/FrobeniusFixedField.lean`;
its SHA-256 is `cda9dddf5f551fc8c81de825093b52cba99d644e45eb274682d2ee986585bfe3`.

Modifications by Worker 5264 on 15 November 2026:

- give the theorem the published proposition `frobeniusClosureDegree_generatorStatement D K L hLK σ` as its type, which the source's first `change` unfolds;
- replace the final step `exact D.extensionNormalizedDegree_frobenius_eq_pow K L hLK σ` (M014.014, not proved in the Library) by that theorem's source proof term `(Exists.choose_spec σ.2).2`, with a comment;
- omit the source `@[simp]` attribute (line 567): the theorem's type is the published target, a definition, not an equation that `simp` can use;
- add the `Langlands.NYLL` namespace prefix and replace the source imports by the Library imports listed above;
- expand `extensionSubgroup K.field L hLK` in the normality binder to its abbreviation body `L.toSubgroup.subgroupOf K.field.toSubgroup`, as in the published target;
- omit `open CyclicCohomology`, the `noncomputable section` and all other source declarations; keep `universe u` and the variable line.

The docstring, the binders and the other proof steps are the source's. The retained original belongs to registered source
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

This module proves only M014.029. It discharges no host class-formation, cup,
transfer, Tate or reciprocity target.

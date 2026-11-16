# The inertia criterion for unramified finite extensions

This module proves the theorem
`Langlands.NYLL.ClassFormation.DegreeData.FiniteAbstractExtension.isUnramified_iff_inertia_le`, the proof phase of
M010.075 in the
[NYLL partition](../../../../../../../../notes/reuse/nyll-public-port/m001-m024.md#m010).
Its type is the published proposition
`Langlands.NYLL.ClassFormation.DegreeData.FiniteAbstractExtension.isUnramified_iff_inertia_leStatement` applied to the
theorem's parameters:

```lean
theorem isUnramified_iff_inertia_le (D : DegreeData G) :
    isUnramified_iff_inertia_leStatement E D
```

## Target and binders

The section variables are those of the published statement module and the source: `{G : Type u} [Group G] [TopologicalSpace G]` and, in `namespace DegreeData.FiniteAbstractExtension`, the explicit `(E : FiniteAbstractExtension G)`. The theorem takes `E` (from the variable) and `D`, exactly as the published target and the source theorem.

By its definition in the published module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Unramified.Statements`, the target is the proposition

```lean
E.IsUnramified D ↔
  E.base.toSubgroup ⊓ D.degree.toMonoidHom.ker ≤ E.field.toSubgroup
```

Here `E : FiniteAbstractExtension G` (M010.065) is an abstract extension of finite index, with base `E.base` and field `E.field` read through its underlying `E.toAbstractExtension`, and `D : DegreeData G` (M010.002) is a degree datum, a continuous homomorphism `D.degree : G →ₜ* ZHatMul` onto `ZHatMul = Multiplicative ZHat` (M010.001, M008.008), whose kernel `D.degree.toMonoidHom.ker` is the inertia subgroup of `G`. `E.IsUnramified D` (M010.071) is unramifiedness of `E.toAbstractExtension`. The target says that `E` is unramified exactly when the inertia subgroup of the base is contained in the subgroup of the field. No hypothesis is added.

## Imports and dependencies

The module imports, unchanged:

- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Unramified.Statements`, which defines the target and imports, through the published `GaloisSubextension.Definitions` and `FiniteExtension.Definitions` modules, `AbstractExtension` (M010.028) with its predicate `IsUnramified` (M010.044), `GaloisSubextension` (M010.052) with `IsUnramified` (M010.055), `FiniteAbstractExtension` (M010.065) with `IsUnramified` (M010.071) and `DegreeData` (M010.002).

The module opens no namespace; the source's `open CyclicCohomology` is not needed, since none of its names occur in the statement or the proof.

## Implemented proof

After `show` states the published proposition unfolded, the proof is `Iff.rfl`. The source proof is the term `E.toAbstractExtension.isUnramified_iff_inertia_le D`, an application of M010.046, whose proof is not in the Library; the port uses the source proof of M010.046 itself, `Iff.rfl`, instead. `Iff.rfl` closes it because both sides are the same proposition after unfolding definitions: `E.IsUnramified D` is by definition (M010.071) `E.toAbstractExtension.IsUnramified D`, which is by definition (M010.044) the containment `E.base.toSubgroup ⊓ D.degree.toMonoidHom.ker ≤ E.field.toSubgroup`.

The development check with `lean_check` in the approved environment compiled the
module with no errors or warnings. This check does not establish independent semantic
acceptance or Integrator publication.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709), commit `fbd320cd8b1b06487c58227e92eb135794267709`. The exact
passage is
[`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Fields.lean`, lines 626–631](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Fields.lean#L626-L631):
the docstring at lines 626–627 and the theorem at lines 628–631. It lies in `namespace ClassFormation` (line 22), with `open CyclicCohomology` (line 24), its `noncomputable section` (line 28), `universe u` (line 30), the variables `{G : Type u} [Group G] [TopologicalSpace G]` (line 46) and `namespace DegreeData` (line 217), `namespace FiniteAbstractExtension` (line 565) and the variable `(E : FiniteAbstractExtension G)` (line 567). The source is:

```lean
/-- Finite unramified extensions satisfy the same inertia-containment
characterization as their underlying abstract extensions. -/
theorem isUnramified_iff_inertia_le (D : DegreeData G) :
    E.IsUnramified D ↔
      E.base.toSubgroup ⊓ D.degree.toMonoidHom.ker ≤ E.field.toSubgroup :=
  E.toAbstractExtension.isUnramified_iff_inertia_le D
```

The complete original file is retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Fields.lean`;
its SHA-256 is `841b30407b1f9f3eb64a30f6ccfa4f8ec555c791564a7e682b7c8ee23c2d156e`.

Modifications by Worker 5264 on 15 November 2026:

- add the `Langlands.NYLL` namespace prefix and replace the source imports by the Library imports listed above;
- give the theorem the published proposition `isUnramified_iff_inertia_leStatement E D` as its type, and begin the proof with `show` stating it unfolded;
- replace the source's term `E.toAbstractExtension.isUnramified_iff_inertia_le D`, which applies the unpublished proof of M010.046, by `exact Iff.rfl`, the source proof of M010.046;
- omit `open CyclicCohomology` and all other source declarations.

The theorem's name, docstring and binders are the source's. The retained original belongs to registered source
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

Worker 5264 wrote this proof and its companion Markdown as the shared draft
for Task 7140; Worker 748 verified and submitted it.

This module proves only M010.075. It discharges no host class-formation, cup,
transfer, Tate or reciprocity target.

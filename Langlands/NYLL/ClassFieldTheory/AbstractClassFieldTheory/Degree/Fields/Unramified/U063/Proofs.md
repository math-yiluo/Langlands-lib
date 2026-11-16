# The inertia criterion for unramified Galois subextensions

This module proves the theorem
`Langlands.NYLL.ClassFormation.DegreeData.GaloisSubextension.isUnramified_iff_inertia_le`, the proof phase of
M010.063 in the
[NYLL partition](../../../../../../../../notes/reuse/nyll-public-port/m001-m024.md#m010).
Its type is the published proposition
`Langlands.NYLL.ClassFormation.DegreeData.GaloisSubextension.isUnramified_iff_inertia_leStatement` applied to the
theorem's parameters:

```lean
theorem isUnramified_iff_inertia_le (L : GaloisSubextension K)
    (D : DegreeData G) :
    isUnramified_iff_inertia_leStatement L D
```

## Target and binders

The section variables are those of the published statement module and the source: `{G : Type u} [Group G] [TopologicalSpace G]` and, in `namespace DegreeData.GaloisSubextension`, `{K : ClosedSubgroup G}`. The theorem takes `L` and `D`, exactly as the published target and the source theorem.

By its definition in the published module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Unramified.Statements`, the target is the proposition

```lean
L.IsUnramified D ↔
  K.toSubgroup ⊓ D.degree.toMonoidHom.ker ≤ L.field.toSubgroup
```

Here `K : ClosedSubgroup G` is an abstract field, `L : GaloisSubextension K` (M010.052) is a Galois subextension of `K`, with closed subgroup `L.field` contained in `K` and normal in it, and `D : DegreeData G` (M010.002) is a degree datum, a continuous homomorphism `D.degree : G →ₜ* ZHatMul` onto `ZHatMul = Multiplicative ZHat` (M010.001, M008.008), whose kernel `D.degree.toMonoidHom.ker` is the inertia subgroup of `G`. `L.IsUnramified D` (M010.055) is unramifiedness of the underlying abstract extension `L.toAbstractExtension`, whose base is `K` and whose field is `L.field`. The target says that `L` is unramified exactly when the inertia subgroup `K ⊓ ker D.degree` is contained in `L.field`. No hypothesis is added.

## Imports and dependencies

The module imports, unchanged:

- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Unramified.Statements`, which defines the target and imports, through the published `GaloisSubextension.Definitions` and `FiniteExtension.Definitions` modules, `AbstractExtension` (M010.028) with its predicate `IsUnramified` (M010.044), `GaloisSubextension` (M010.052) with `IsUnramified` (M010.055), `FiniteAbstractExtension` (M010.065) with `IsUnramified` (M010.071) and `DegreeData` (M010.002).

The module opens no namespace; the source's `open CyclicCohomology` is not needed, since none of its names occur in the statement or the proof.

## Implemented proof

After `show` states the published proposition unfolded, the proof is `Iff.rfl`. The source proof is the term `L.toAbstractExtension.isUnramified_iff_inertia_le D`, an application of M010.046, whose proof is not in the Library; the port uses the source proof of M010.046 itself, `Iff.rfl`, instead. `Iff.rfl` closes it because both sides are the same proposition after unfolding definitions: `L.IsUnramified D` is by definition (M010.055) `L.toAbstractExtension.IsUnramified D`, which is by definition (M010.044) the containment `L.toAbstractExtension.base.toSubgroup ⊓ D.degree.toMonoidHom.ker ≤ L.toAbstractExtension.field.toSubgroup`, and the base and field of `L.toAbstractExtension` are `K` and `L.field`.

The development check with `lean_check` in the approved environment compiled the
module with no errors or warnings. This check does not establish independent semantic
acceptance or Integrator publication.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709), commit `fbd320cd8b1b06487c58227e92eb135794267709`. The exact
passage is
[`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Fields.lean`, lines 535–540](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Fields.lean#L535-L540):
the docstring at line 535 and the theorem at lines 536–540. It lies in `namespace ClassFormation` (line 22), with `open CyclicCohomology` (line 24), its `noncomputable section` (line 28), `universe u` (line 30), the variables `{G : Type u} [Group G] [TopologicalSpace G]` (line 46) and `namespace DegreeData` (line 217), `namespace GaloisSubextension` (line 467) and the variable `{K : ClosedSubgroup G}` (line 469). The source is:

```lean
/-- Unramifiedness is the canonical inertia-containment condition. -/
theorem isUnramified_iff_inertia_le (L : GaloisSubextension K)
    (D : DegreeData G) :
    L.IsUnramified D ↔
      K.toSubgroup ⊓ D.degree.toMonoidHom.ker ≤ L.field.toSubgroup :=
  L.toAbstractExtension.isUnramified_iff_inertia_le D
```

The complete original file is retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Fields.lean`;
its SHA-256 is `841b30407b1f9f3eb64a30f6ccfa4f8ec555c791564a7e682b7c8ee23c2d156e`.

Modifications by Worker 5264 on 15 November 2026:

- add the `Langlands.NYLL` namespace prefix and replace the source imports by the Library imports listed above;
- give the theorem the published proposition `isUnramified_iff_inertia_leStatement L D` as its type, and begin the proof with `show` stating it unfolded;
- replace the source's term `L.toAbstractExtension.isUnramified_iff_inertia_le D`, which applies the unpublished proof of M010.046, by `exact Iff.rfl`, the source proof of M010.046;
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

This module proves only M010.063. It discharges no host class-formation, cup,
transfer, Tate or reciprocity target.

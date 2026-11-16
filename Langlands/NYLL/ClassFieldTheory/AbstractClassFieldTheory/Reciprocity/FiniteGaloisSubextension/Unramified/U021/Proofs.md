# The inertia criterion for unramified finite Galois subextensions

This module proves the theorem
`Langlands.NYLL.ClassFormation.FiniteGaloisSubextension.isUnramified_iff_inertia_le`, the proof phase of
M040.021 in the
[NYLL partition](../../../../../../../../notes/reuse/nyll-public-port/m025-m048.md#m040).
Its type is the published proposition
`Langlands.NYLL.ClassFormation.FiniteGaloisSubextension.isUnramified_iff_inertia_leStatement` applied to the
theorem's parameters:

```lean
theorem isUnramified_iff_inertia_le (L : FiniteGaloisSubextension K)
    (D : DegreeData G) :
    isUnramified_iff_inertia_leStatement L D
```

## Target and binders

The section variables are those of the published statement module and the source: `{G : Type u} [Group G] [TopologicalSpace G]`, in `section GroupOnly`, and, in `namespace FiniteGaloisSubextension`, `{K : ClosedSubgroup G}`. The theorem takes `L` and `D`, exactly as the published target and the source theorem.

By its definition in the published module `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension.Unramified.Statements`, the target is the proposition

```lean
L.IsUnramified D ↔
  K.toSubgroup ⊓ D.degree.toMonoidHom.ker ≤ L.field.toSubgroup
```

Here `K : ClosedSubgroup G` is an abstract field, `L : FiniteGaloisSubextension K` (M040.001) is a finite Galois subextension of `K`, with closed subgroup `L.field` normal and of finite index in `K`, and `D : DegreeData G` (M010.002) is a degree datum, a continuous homomorphism `D.degree : G →ₜ* ZHatMul` onto `ZHatMul = Multiplicative ZHat` (M010.001, M008.008), whose kernel `D.degree.toMonoidHom.ker` is the inertia subgroup of `G`. `L.IsUnramified D` (M040.005) is unramifiedness of the underlying finite abstract extension `L.toFiniteAbstractExtension`, whose base is `K` and whose field is `L.field`. The target says that `L` is unramified exactly when the inertia subgroup `K ⊓ ker D.degree` is contained in `L.field`. No hypothesis is added.

## Imports and dependencies

The module imports, unchanged:

- `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension.Unramified.Statements`, which defines the target and imports, through the published `FiniteGaloisSubextension.Definitions` module, `FiniteGaloisSubextension` (M040.001) with its predicate `IsUnramified` (M040.005), `FiniteAbstractExtension` (M010.065) with `IsUnramified` (M010.071), `AbstractExtension.IsUnramified` (M010.044) and `DegreeData` (M010.002).

The module opens no namespace; the source's `open KummerTheory` and `open CyclicCohomology` are not needed, since none of their names occur in the statement or the proof.

## Implemented proof

After `show` states the published proposition unfolded, the proof is `Iff.rfl`. The source proof is the term `L.toFiniteAbstractExtension.isUnramified_iff_inertia_le D`, an application of M010.075, which in turn applies M010.046; neither proof is in the Library, and the port uses the source proof of M010.046, `Iff.rfl`, instead. `Iff.rfl` closes it because both sides are the same proposition after unfolding definitions: `L.IsUnramified D` is by definition (M040.005) `L.toFiniteAbstractExtension.IsUnramified D`, which unfolds through M010.071 and M010.044 to the containment of `K.toSubgroup ⊓ D.degree.toMonoidHom.ker` in `L.field.toSubgroup`, since the base and field of `L.toFiniteAbstractExtension` are `K` and `L.field`.

The development check with `lean_check` in the approved environment compiled the
module with no errors or warnings. This check does not establish independent semantic
acceptance or Integrator publication.

## Original passage and modifications

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709), commit `fbd320cd8b1b06487c58227e92eb135794267709`. The exact
passage is
[`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FiniteGaloisSubextension.lean`, lines 197–202](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FiniteGaloisSubextension.lean#L197-L202):
the docstring at line 197 and the theorem at lines 198–202. It lies in `namespace ClassFormation` (line 17), with `open KummerTheory` (line 19) and `open CyclicCohomology` (line 21), its `noncomputable section` (line 25), `universe u` (line 27), `section GroupOnly` (line 29), the variables `{G : Type u} [Group G] [TopologicalSpace G]` (line 31), `namespace FiniteGaloisSubextension` (line 44) and the variable `{K : ClosedSubgroup G}` (line 46). The source is:

```lean
/-- Unramifiedness is the canonical inertia-containment condition. -/
theorem isUnramified_iff_inertia_le (L : FiniteGaloisSubextension K)
    (D : DegreeData G) :
    L.IsUnramified D ↔
      K.toSubgroup ⊓ D.degree.toMonoidHom.ker ≤ L.field.toSubgroup :=
  L.toFiniteAbstractExtension.isUnramified_iff_inertia_le D
```

The complete original file is retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/FiniteGaloisSubextension.lean`;
its SHA-256 is `c3b543d031492dac28deef22332941e7ff6bda845aa34e8be3ecd6c59d87098e`.

Modifications by Worker 5264 on 15 November 2026:

- add the `Langlands.NYLL` namespace prefix and replace the source imports by the Library imports listed above;
- give the theorem the published proposition `isUnramified_iff_inertia_leStatement L D` as its type, and begin the proof with `show` stating it unfolded;
- replace the source's term `L.toFiniteAbstractExtension.isUnramified_iff_inertia_le D`, which applies the unpublished proof of M010.075, by `exact Iff.rfl`, the source proof of M010.046 to which M010.075 reduces;
- omit `open KummerTheory`, `open CyclicCohomology` and all other source declarations.

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

This module proves only M040.021. It discharges no host class-formation, cup,
transfer, Tate or reciprocity target.

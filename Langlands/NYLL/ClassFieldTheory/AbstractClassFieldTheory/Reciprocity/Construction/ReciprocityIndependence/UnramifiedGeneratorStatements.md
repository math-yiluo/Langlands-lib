# NYLL M033.016: degree-one lifts generate a finite unramified Galois quotient

This module extracts one public theorem signature of Naganori Yamaguchi's
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/ReciprocityIndependence.lean`
at pinned commit `fbd320cd8b1b06487c58227e92eb135794267709` of
`n-yamaguchi-0729/ClassFieldTheory`. The original file SHA-256 is
`169ddc13c58e7f6ef6ae39a433fb381c533464174c4245210c8bec5d69ffd5e4`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The readable original is in the project's literature collection under
`External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.

| Unit | Source lines | Original theorem | Adapted target |
| --- | --- | --- | --- |
| M033.016 | 275–290 | `ClassFormation.DegreeData.quotient_generator_of_unramified_degree_one` | `Langlands.NYLL.ClassFormation.DegreeData.quotient_generator_of_unramified_degree_oneStatement` |

Lines 275–277 are the source docstring and lines 278–290 the signature (ending in `:= by`). The
proof, which starts at line 291 and uses M012.013 `frobeniusRestriction_surjective`,
is omitted.

## The objects

All data are the actual published source definitions.

- `G : Type u` with `[Group G] [TopologicalSpace G]` (source line 31).
- `D : DegreeData G` (M010.002) is the source degree datum, with continuous
  surjective degree homomorphism `D.degree : G →ₜ* ZHatMul`, where
  `ZHatMul = Multiplicative ZHat` (M010.001) and `ZHat` is M008.008.
- `K : FiniteResidueAbstractField D` (M010.021) is a closed subgroup `K.field`
  (the absolute Galois group `G_K`) with finite residue quotient.
- `L : ClosedSubgroup G` with `hLK : L.toSubgroup ≤ K.field.toSubgroup` is a
  field `L` above `K`.
- `extensionSubgroup K.field L hLK` (M004.002, the published abbreviation
  `Langlands.NYLL.CyclicCohomology.extensionSubgroup`, module
  `Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions`)
  is `L.toSubgroup.subgroupOf K.field.toSubgroup`, the subgroup `G_L` of `G_K`.
  The quotient `K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK` is the
  Galois group `G(L|K)`.
- `DegreeData.AbstractExtension.mk L K.field hLK : AbstractExtension G`
  (M010.028, constructor of the published structure) is the abstract extension
  `L|K`, and `AbstractExtension.IsUnramified E D` (published, module
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.AbstractExtension.StructuralDefinitions`)
  is `E.base.toSubgroup ⊓ D.degree.toMonoidHom.ker ≤ E.field.toSubgroup`.
- `D.normalizedDegree K : K.field.toSubgroup →ₜ* ZHatMul` (M011.006, module
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Frobenius.NormalizedDegree.Definitions`)
  is the normalized degree `d_K = (1 / f_K) d`.

## Statement

`quotient_generator_of_unramified_degree_oneStatement (D : DegreeData G) (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.field.toSubgroup) [hnormal : (extensionSubgroup K.field L hLK).Normal] [hfinite : Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)] (hUnramified : (DegreeData.AbstractExtension.mk L K.field hLK).IsUnramified D) (φ : K.field.toSubgroup) (hφ : D.normalizedDegree K φ = Multiplicative.ofAdd (1 : ZHat)) : Prop`
is

```lean
∀ x : K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK,
  x ∈ Subgroup.zpowers (QuotientGroup.mk φ)
```

that is, if `L|K` is a finite unramified Galois extension and `φ ∈ G_K` has
normalized degree `d_K(φ) = 1`, then the class of `φ` generates `G(L|K)`.

The target has the source universe `u`, the implicit `G : Type u` followed by
the instance binders `[Group G]` and `[TopologicalSpace G]`, then exactly the
source binders `D`, `K`, `L`, `hLK`, the named instance binders `hnormal` and
`hfinite`, and the explicit `hUnramified`, `φ` and `hφ`, in source order and
with the source binder kinds. No hypothesis is added or dropped. The
conclusion does not mention `hfinite`, `hUnramified` or `hφ`; they are kept
because the source theorem has them, and the source proof uses them.

## Modifications

Worker 5264 makes these modifications:

- Extract only this theorem signature, with the source's `universe u`
  (line 17), namespace `ClassFormation`, `open CyclicCohomology` (line 23),
  noncomputable section (line 27), section `groupTheoreticRefinements`
  (line 29), its variable declaration (line 31) and namespace `DegreeData`
  (line 273). Omit the proof and all other source declarations.
- Omit the source's `open KummerTheory` (line 21): nothing in the signature
  uses it.
- Prefix the namespace `ClassFormation` with `Langlands.NYLL` and append
  `Statement` to the theorem name. The theorem's conclusion becomes the body of
  a `Prop`-valued definition with the same parameters.
- Prefix the source docstring with "Target:".
- Add `set_option linter.unusedVariables false in` before the definition. Its
  conclusion does not use the source hypotheses `hfinite`, `hUnramified` and
  `hφ`, so the linter would flag them. The option changes no declaration.
- Replace the source imports
  `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.UnitCohomologyAxiom`
  and `...Reciprocity.Construction.ReciprocityDefinition` with three focused
  published modules: the normalized-degree definitions module
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Frobenius.NormalizedDegree.Definitions`
  (for `normalizedDegree`, and transitively the degree datum, `ZHat` and
  finite-residue fields), the abstract-extension module
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.AbstractExtension.StructuralDefinitions`
  (for `AbstractExtension` and `IsUnramified`) and
  `Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions`
  (for `extensionSubgroup`).
- Retain the original copyright, Apache-2.0 and author header, and add the
  explicit modification record in the Lean module documentation.

The module supplies no proof. The proof of this target is a separate unit. In
the source it uses M012.013 `frobeniusRestriction_surjective` and the
normalized-degree identities of M011.

The existing `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are retained,
with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

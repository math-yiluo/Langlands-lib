# NYLL M033.017: finite unramified Galois quotients are cyclic

The paired Lean file gives the Prop-valued target
`Langlands.NYLL.ClassFormation.DegreeData.exists_quotient_generator_of_unramifiedStatement`
for the source theorem
`ClassFormation.DegreeData.exists_quotient_generator_of_unramified`. The
source is Naganori Yamaguchi's ClassFieldTheory (NYLL) at commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/ReciprocityIndependence.lean`
(file SHA-256
`169ddc13c58e7f6ef6ae39a433fb381c533464174c4245210c8bec5d69ffd5e4`),
inventory unit M033.017. The theorem occupies lines 344–362: the docstring
is at 344–346, the signature at 347–357 (the conclusion is at 356–357,
ending with `:= by`) and the proof at 358–362. The section context is at lines
17–31: `universe u`, `namespace ClassFormation`, the opens `KummerTheory`
and `CyclicCohomology`, `noncomputable section`,
`section groupTheoreticRefinements` and the variables
`{G : Type u} [Group G] [TopologicalSpace G]`; the theorem lies in
`namespace DegreeData` (lines 273–364). The registered source
`external-lean-reuse-snapshots-2026-10-21` (folder
`n-yamaguchi-0729--ClassFieldTheory/source`) has content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

## The statement

The parameters are, in the source order and with the source binder kinds:

- implicit `G : Type u` and instance arguments `[Group G]` and
  `[TopologicalSpace G]`, from the section variables;
- explicit `D : DegreeData G`, the Library's
  `Langlands.NYLL.ClassFormation.DegreeData` (M010.002): a continuous
  surjective degree homomorphism `d : G → Ẑ`;
- explicit `K : FiniteResidueAbstractField D`, the Library's
  `Langlands.NYLL.ClassFormation.DegreeData.FiniteResidueAbstractField`
  (M010.021): a closed subgroup `K.field = G_K` whose residue quotient is
  finite;
- explicit `L : ClosedSubgroup G`, the subgroup `G_L` of the top field;
- explicit `hLK : L.toSubgroup ≤ K.field.toSubgroup`, i.e. `G_L ≤ G_K`;
- instance argument
  `[hnormal : (extensionSubgroup K.field L hLK).Normal]`: `G_L` is normal in
  `G_K`, so `L | K` is Galois and the quotient `G_K / G_L` is a group;
- instance argument
  `[_hfinite : Finite (K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK)]`:
  the quotient `G_K / G_L` is finite (source name `hfinite`);
- explicit
  `_hUnramified : (DegreeData.AbstractExtension.mk L K.field hLK).IsUnramified D`
  (source name `hUnramified`): the extension is unramified. Here
  `DegreeData.AbstractExtension` is the Library's
  `Langlands.NYLL.ClassFormation.DegreeData.AbstractExtension` (M010.028),
  the structure with fields `field`, `base` and `below`, and its
  `IsUnramified D` is the Library predicate
  `E.base.toSubgroup ⊓ D.degree.toMonoidHom.ker ≤ E.field.toSubgroup`. So
  the hypothesis says `G_K ∩ ker d ≤ G_L`: the inertia of `K` lies in `G_L`.

`extensionSubgroup` is the Library's
`Langlands.NYLL.CyclicCohomology.extensionSubgroup` (M004.002), the
abbreviation for `L.toSubgroup.subgroupOf K.toSubgroup`; it is reached by
name through `open CyclicCohomology`, as in the source.

The body, which is the source conclusion verbatim, is

```lean
∃ g : K.field.toSubgroup ⧸ extensionSubgroup K.field L hLK,
    ∀ x, x ∈ Subgroup.zpowers g
```

It says that the finite quotient group `G_K / G_L` has an element `g` whose
integer powers give every element, so `Gal(L | K)` is cyclic. The group
structure on the quotient is Mathlib's `QuotientGroup` structure from the
normality instance `hnormal`. The source docstring adds that the generator
can be taken to be the restriction of an element of degree `1`; the
conclusion itself states only the existence of a generator, and so does the
target.

## Modifications

Worker 483 made these changes to the source:

- The namespace `ClassFormation` becomes `Langlands.NYLL.ClassFormation`.
- `Statement` is appended to the name. The `theorem` becomes a `def`
  returning `Prop` whose body is the source conclusion.
- The argument names `hfinite` and `hUnramified` gain leading underscores
  because the body does not refer to these proofs (Lean's unused-variable
  linter otherwise warns). Both parameters keep their position, binder kind
  (instance for `_hfinite`, explicit for `_hUnramified`) and full types, so a
  proof of the target takes them in the source order. `hnormal` is used by
  the body, through the quotient group structure, and keeps its name.
- The proof (lines 358–362) is not ported. Proving the target is a separate
  `lean.proof@1` task. The source proof uses `D.normalizedDegree_surjective`
  and `D.quotient_generator_of_unramified_degree_one`, which are not needed
  to state the target.
- The docstring is adapted to say that the definition is a target and to
  describe only what the body states (a generator exists); the source
  docstring's remark about a degree-`1` lift describes its proof.
- The module holds only this target, in the subdirectory
  `ReciprocityIndependence/QuotientGenerator/` so that it does not collide
  with the sibling task's modules under `ReciprocityIndependence/`. The
  other declarations of the source module are omitted.
- `open KummerTheory` is omitted: the statement does not use it, and the
  Library has no such namespace. `open CyclicCohomology`, `universe u`,
  `noncomputable section` and the section and variable lines are kept.
- The source imports
  `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.UnitCohomologyAxiom`
  and `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.ReciprocityDefinition`
  are replaced by the focused Library imports
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteResidue.Definitions`
  (for `DegreeData` and `FiniteResidueAbstractField`),
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.AbstractExtension.StructuralDefinitions`
  (for `AbstractExtension` and `IsUnramified`) and
  `Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions`
  (for `extensionSubgroup`).

A focused `lean_check` of this module, with the declaration inspected,
reports no errors or warnings, `statement_returns_prop: true` and the single
universe parameter `u`. The target needs only published Library
declarations; it does not use `FiniteIntermediateField`.

## Scope

This unit states M033.017 and does not prove it. No reciprocity,
class-formation or cohomological theorem is asserted here.

## Licence

The original copyright, Apache-2.0 release and author header are kept at the
top of the Lean file, followed by a modification notice. The retained files
are `licenses/NYLL/LICENSE`, SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`,
and `licenses/NYLL/NOTICE`, SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

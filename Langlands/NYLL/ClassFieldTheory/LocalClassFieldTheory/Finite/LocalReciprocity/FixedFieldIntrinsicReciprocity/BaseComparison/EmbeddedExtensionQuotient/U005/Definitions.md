# The ambient embedded extension quotient is the Galois group

This module defines
`Langlands.NYLL.LocalClassFieldTheory.ambientEmbeddedExtensionQuotientEquivGaloisGroup`,
the port of source row M274.005. Take a tower of fields `K ⊆ F ⊆ E` with
`F / K` finite separable and `E / F` finite Galois, and a `K`-embedding
`j` of `E` into `SeparableClosure K`. Inside
`Gal(SeparableClosure K / K)`, consider the closed subgroup fixing the image
of `F` and its subgroup fixing the image of `E`. The quotient of the first by
the second is identified with `Gal(E / F)`. The equivalence is built by
moving to the separable closure of `F` along a chosen `F`-isomorphism `e`.

## Parameters and type

The definition takes, in the source order,

```lean
(K F E : Type) [Field K] [Field F] [Field E]
  [Algebra K F] [Algebra F E] [Algebra K E]
  [IsScalarTower K F E]
  [FiniteDimensional K F] [Algebra.IsSeparable K F]
  [FiniteDimensional F E] [IsGalois F E]
  (j : E →ₐ[K] SeparableClosure K)
```

These binders are written in the definition's own signature (not as section
variables), so all of them are arguments of the elaborated constant,
including any that the body does not use. All fields
are in `Type` (universe zero), as in the source. There is no valuation,
topology or local-field hypothesis.

The result type is the source's, verbatim:

```lean
let i := j.comp (IsScalarTower.toAlgHom K F E)
letI : Algebra F (SeparableClosure F) :=
  (separableClosure F (AlgebraicClosure F)).algebra
letI : Algebra F (SeparableClosure K) := i.toRingHom.toAlgebra
∀ e : SeparableClosure F ≃ₐ[F] SeparableClosure K,
  let H₀ := closedFixingSubgroup K (SeparableClosure K) (AlgHom.fieldRange i)
  let J₀ := closedFixingSubgroup K (SeparableClosure K) (AlgHom.fieldRange j)
  let hJH : J₀.toSubgroup ≤ H₀.toSubgroup := by
    change
      (AlgHom.fieldRange j).fixingSubgroup ≤
        (AlgHom.fieldRange i).fixingSubgroup
    apply (AlgHom.fieldRange i).fixingSubgroup_le
    intro x hx
    rcases hx with ⟨y, rfl⟩
    exact ⟨algebraMap F E y, rfl⟩
  letI hTargetNormal : (extensionSubgroup H₀ J₀ hJH).Normal :=
    ambientEmbeddedExtensionSubgroup_normal K F E j e
  (H₀.toSubgroup ⧸ extensionSubgroup H₀ J₀ hJH) ≃* Gal(E / F)
```

Here:

- `i : F →ₐ[K] SeparableClosure K` is the restriction of `j` to `F`.
- The first local instance is the algebra structure of the intermediate
  field `separableClosure F (AlgebraicClosure F)`, which is how Mathlib
  defines `SeparableClosure F`. The second makes `SeparableClosure K` an
  `F`-algebra through `i`.
- `e` is any `F`-algebra isomorphism `SeparableClosure F ≃ₐ[F]
  SeparableClosure K` for these structures. Applied to `e`, the definition
  returns the equivalence.
- `H₀` and `J₀` are the closed subgroups of `Gal(SeparableClosure K / K)`
  fixing `i(F)` and `j(E)`. The inclusion `hJH` holds because
  `i y = j (algebraMap F E y)`, so `i(F) ⊆ j(E)`.
- The Library `extensionSubgroup H₀ J₀ hJH` (source row M004.002) is the
  subgroup `J₀.toSubgroup.subgroupOf H₀.toSubgroup` of `H₀.toSubgroup`.
- The group structure on the quotient comes from the local instance
  `hTargetNormal`. It is given by the published theorem
  `ambientEmbeddedExtensionSubgroup_normal` (M274.003). In the Library that
  theorem proves the closed proposition
  `ambientEmbeddedExtensionSubgroup_normalStatement`, whose conclusion is
  `(J₀.toSubgroup.subgroupOf H₀.toSubgroup).Normal` for the same local data.
  The source term `ambientEmbeddedExtensionSubgroup_normal K F E j e`
  elaborates unchanged against it: Lean unfolds the proposition to apply it
  to these arguments, and its conclusion agrees with
  `(extensionSubgroup H₀ J₀ hJH).Normal` by unfolding `extensionSubgroup`.

## Content

The body is the source tactic block. Only the proof of the local fact `hmap`
is changed (see below). After
`dsimp only` it introduces `i` and the `F`-algebra structure on
`SeparableClosure K` again, takes `e` by `intro e`, and introduces the
following local data, as in the published M274.001/M274.002 statements:

- `jF : E →ₐ[F] SeparableClosure K`, the map `j` regarded as an `F`-algebra
  map, and `jI := e.symm.toAlgHom.comp jF : E →ₐ[F] SeparableClosure F`, the
  matching embedding of `E` into the separable closure of `F`;
- `EI := finiteGaloisAbstractExtensionOfEmbedding F E jI` (M097.005), the
  finite abstract extension object of `E / F` attached to `jI`;
- `H₀`, `J₀`, `hRange : AlgHom.fieldRange i ≤ AlgHom.fieldRange j` and `hJH`;
- `psi := intrinsicBaseEquivAmbientEmbeddedField K F i e` (M273.006), the
  equivalence from the intrinsic base subgroup `intrinsicAbstractBase F` of
  `Gal(SeparableClosure F / F)` onto `H₀`;
- the local instances `hSourceNormal := EI.normal`, normality of the
  intrinsic extension subgroup, and `hTargetNormal` as in the type;
- `hmap`, the equality of the image of the intrinsic extension subgroup under
  `psi` with `extensionSubgroup H₀ J₀ hJH`.

The source obtains `hmap` by `simpa only` from the M274.002 theorem
`map_intrinsicExtensionSubgroup_eq_ambientEmbeddedField`. The Library has the
statement of that theorem (closed proposition
`map_intrinsicExtensionSubgroup_eq_ambientEmbeddedFieldStatement`), but its
proof (Task 6708) is not yet published. The port therefore proves `hmap` in
the body, following the source proofs of M274.001 and M274.002:

- `hval`: for every `tau` and `x`, `(psi tau).1.1 x = e (tau.1 (e.symm x))`.
  This is the published theorem
  `intrinsicBaseEquivAmbientEmbeddedField_apply_val` (M273.008) applied to
  `K F i e`.
- `hmem`: for every `tau` in `intrinsicAbstractBase F`, `tau` lies in the
  intrinsic extension subgroup exactly when `psi tau` lies in
  `extensionSubgroup H₀ J₀ hJH`. After `change`, both sides are membership in
  fixing subgroups, of the field range of `jI` and of `j`. Each direction
  takes `y : E` and compares `tau` at `jI y = e.symm (j y)` with `psi tau` at
  `j y`, using `hval`, `e.apply_symm_apply` and the injectivity of `e`. This
  is the source proof of M274.001.
- `hmap`, by `ext sigma`: an image `psi tau` lies in the target by `hmem`;
  conversely `sigma` is the image of `psi.symm sigma`, which lies in the
  intrinsic extension subgroup by `hmem`. This is the source proof of
  M274.002.

`hmap` is a proposition, so its proof does not affect the defined
equivalence. The elaborated type is unchanged too: a development build with
the unchanged source body, using the draft proof of M274.002 from Task 6708,
gave the same SHA-256 fingerprint of the type representation.

The result is the composite

```lean
(QuotientGroup.congr
  (extensionSubgroup (intrinsicAbstractBase F) EI.field EI.below)
  (extensionSubgroup H₀ J₀ hJH)
  psi hmap).symm.trans
  (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding F E jI)
```

So the ambient quotient is first carried back, through `psi`, to the quotient
of `intrinsicAbstractBase F` by the intrinsic extension subgroup of `EI`.
Then the published
`finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding F E jI` (M090.009)
identifies that quotient with `Gal(E / F)`. That last step is legitimate
because `intrinsicAbstractBase F` is by definition
`closedFixingSubgroup F (SeparableClosure F) ⊥`, and `EI.field` is
`finiteGaloisClosedFixingSubgroupOfEmbedding F E jI`. Both identifications
hold by unfolding definitions.

## Reused Library declarations

| Source unit and original declaration | Library declaration used |
| --- | --- |
| M097.005, `LocalClassFieldTheory.finiteGaloisAbstractExtensionOfEmbedding` | `Langlands.NYLL.LocalClassFieldTheory.finiteGaloisAbstractExtensionOfEmbedding` (module `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ConcreteReciprocityTransport.Extension.Definitions`) |
| M273.008, `LocalClassFieldTheory.intrinsicBaseEquivAmbientEmbeddedField_apply_val` | `Langlands.NYLL.LocalClassFieldTheory.intrinsicBaseEquivAmbientEmbeddedField_apply_val` (module `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.BaseComparison.IntrinsicBaseEquivalence.U008.Proofs`) |
| M274.003, `LocalClassFieldTheory.ambientEmbeddedExtensionSubgroup_normal` | `Langlands.NYLL.LocalClassFieldTheory.ambientEmbeddedExtensionSubgroup_normal` (module `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.BaseComparison.EmbeddedExtensionQuotient.U003.Proofs`) |
| M090.009, `LocalClassFieldTheory.finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding` | `Langlands.NYLL.LocalClassFieldTheory.finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding` (module `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteGaloisRealization.Quotient.Definitions`) |
| M273.006, `LocalClassFieldTheory.intrinsicBaseEquivAmbientEmbeddedField` | `Langlands.NYLL.LocalClassFieldTheory.intrinsicBaseEquivAmbientEmbeddedField` (module `...FixedFieldIntrinsicReciprocity.BaseComparison.IntrinsicBaseEquivalence.U004.Definitions`, imported through the U008 Proofs module) |
| M091.003, `LocalClassFieldTheory.intrinsicAbstractBase` | `Langlands.NYLL.LocalClassFieldTheory.intrinsicAbstractBase` (module `...LocalReciprocity.IntrinsicAbsoluteData.Initial.Definitions`, imported through the other modules) |
| M087.001, `RamificationTheory.closedFixingSubgroup` | `Langlands.NYLL.RamificationTheory.closedFixingSubgroup` (module `Langlands.NYLL.ValuedFieldTheory.Ramification.GaloisValuation.ClosedFixingSubgroup.Definitions`, imported through the other modules) |
| M004.002, `CyclicCohomology.extensionSubgroup` | `Langlands.NYLL.CyclicCohomology.extensionSubgroup` (module `Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions`, imported through the other modules) |

The four imported modules are those in the first four rows. They import the
other modules listed. The names are reached through the source's
`open RamificationTheory CyclicCohomology` line inside the namespace
`Langlands.NYLL.LocalClassFieldTheory`. The M274.002 theorem
`map_intrinsicExtensionSubgroup_eq_ambientEmbeddedField` cited by the source
is not used, because its proof is not yet in the Library (see Content).

## Relation to other Library and Mathlib declarations

A search of the Library `.lean` files at commit
`544dba099880b57da5fdc3cbc715c01cf2579eb2` found no declaration named
`ambientEmbeddedExtensionQuotientEquivGaloisGroup`. It also found no other
equivalence between `H₀ ⧸ extensionSubgroup H₀ J₀ hJH` and `Gal(E / F)` for
an embedded tower. The related declarations are:

- `Langlands.NYLL.LocalClassFieldTheory.baseFixingExtensionQuotientEquivGaloisGroup`
  (M089.011, `...LocalReciprocity.GaloisExtensionQuotient.Quotient.Definitions`)
  handles the case where the base is the whole group: it identifies the
  quotient of `closedFixingSubgroup K Ω ⊥` by the extension subgroup of an
  intermediate field `E` of a Galois extension `Ω / K` with `Gal(E / K)`.
  M090.009, used in the body, specializes it to the field range of an
  embedding.
- `Langlands.NYLL.LocalClassFieldTheory.abstractExtensionQuotientEquivGaloisGroup`
  (`...LocalReciprocity.FiniteAbstractFixedField.Equivalences.Definitions`)
  takes closed subgroups `L ≤ K` of `Gal(Ω / k)` with `L` normal in `K`. It
  identifies `K ⧸ L` with the Galois group of the abstract fixed field of `L`
  over that of `K`, both intermediate fields of `Ω`. Applied to `J₀ ≤ H₀`, its
  target would be the Galois group of two fixed fields inside
  `SeparableClosure K`. It is not the given `Gal(E / F)`, and it requires the
  normality hypothesis as an argument.
- `Langlands.ClassFieldTheory.Local.fixedFieldRestrictedGroupEquiv`
  (`Langlands/ClassFieldTheory/Local/FixedFieldStageRestriction.lean`)
  identifies `E.fixingSubgroup ⧸ N.toSubgroup.comap E.fixingSubgroup.subtype`
  with `Gal(fixedField N / E)`, for a closed subgroup `N` of `Gal(L / K)` that
  is normal in the whole group. In the present setting `J₀` need not be normal
  in `Gal(SeparableClosure K / K)`, because `E / K` need not be normal. Its
  target is also the automorphism group of an intermediate field of `L / K`,
  not the abstract `Gal(E / F)`.
- `Langlands.ClassFieldTheory.Local.finiteGaloisStageGroupEquiv`
  (`Langlands/ClassFieldTheory/Local/FixedFieldStages.lean`) identifies the
  absolute Galois group of `K`, taken in `AlgebraicClosure K`, modulo the
  fixing subgroup of a finite Galois intermediate field `E` with `Gal(E / K)`.
  This is a base-field case only.
- Mathlib's `IsGalois.normalAutEquivQuotient` and
  `InfiniteGalois.normalAutEquivQuotient` identify Galois-group quotients by
  normal subgroups with Galois groups of fixed fields over the base field.
  They are not stated for an intermediate base subgroup such as `H₀`.

None of these is the present definition, so the port is not a duplicate.

## Original source

The original source is Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/BaseComparison/EmbeddedExtensionQuotient.lean`](</home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/BaseComparison/EmbeddedExtensionQuotient.lean>).
The complete file was read and its SHA-256 verified as
`6d057d4d7df649ce5d67657b86688b0532b975cbc5d03be5b15582dccdc140da`.
The M274.005 docstring occupies lines 394–395, its signature lines 396–429
and its body lines 430–482. The header occupies lines 1–5, the import of
`IntrinsicBaseEquivalence` line 8, the `noncomputable section` line 20, the
namespace line 22 and the `open` lines 24–26.

| Source unit and original declaration | Adapted declaration |
| --- | --- |
| M274.005, `LocalClassFieldTheory.ambientEmbeddedExtensionQuotientEquivGaloisGroup` (def) | `Langlands.NYLL.LocalClassFieldTheory.ambientEmbeddedExtensionQuotientEquivGaloisGroup` |

The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
with supplement `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

## Modifications and attribution

Worker 57 made these changes:

- The namespace `LocalClassFieldTheory` is prefixed with `Langlands.NYLL`.
  The definition is placed in its own module
  `BaseComparison/EmbeddedExtensionQuotient/U005/Definitions`.
- The source imports `Mathlib.FieldTheory.Galois.Basic` and the broad module
  `...BaseComparison.IntrinsicBaseEquivalence` (lines 7–8). The port instead
  imports the four published modules in the first four rows of the table
  above. Together they supply every declaration the definition uses.
- The source opens `LocalFieldTheory`, `KummerTheory`, `ClassFormation` and
  `ValuativeRel` (scoped); the definition uses none of these. The port omits
  them and keeps `open RamificationTheory CyclicCohomology`.
- The docstring, the `noncomputable def` keyword, the binders and the result
  type are copied from source lines 394–429 without change. The body is
  copied from source lines 430–482, except that the proof of `hmap` (source
  lines 467–474) is replaced by the local facts `hval`, `hmem` and `hmap`
  described under Content, with explanatory comments. These are the source
  proofs of M274.001 (lines 71–125) and M274.002 (lines 170–217), with the
  pointwise formula taken from the published M273.008 theorem. The
  definition sits inside a `noncomputable section` that, as in the source, is
  opened before the namespace and is not closed.
- No other declaration of the source file is included. The other source
  declarations this definition uses are the published ones listed above.

The Lean header keeps the original 2026 Naganori Yamaguchi copyright,
the authorship line including OpenAI Codex assistance, and the Apache-2.0
notice. A dated modification record follows it. The existing
[LICENSE](../../../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../../../licenses/NYLL/NOTICE) match the pinned
upstream files.

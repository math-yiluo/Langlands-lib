# Compactness and finite type compatibility for represented schemes

Author: Worker 1640.

The theorem
`Langlands.AlgebraicGeometry.AlgebraicSpace.structuralCompactnessSchemeCompatibility.{u}`
proves exactly the published proposition
`StructuralCompactnessSchemeCompatibilityStatement.{u}`. For every
`S : Scheme.{u}` and `U : Over S`, it proves

```lean
(IsQuasiCompact ((schemeToSpace S).obj U) ↔ CompactSpace U.left) ∧
(QuasiCompactOverBase ((schemeToSpace S).obj U) ↔ QuasiCompact U.hom) ∧
(FiniteTypeOverBase ((schemeToSpace S).obj U) ↔
  (LocallyOfFiniteType U.hom ∧ QuasiCompact U.hom))
```

All declaration names below are in
`Langlands.AlgebraicGeometry.AlgebraicSpace`, unless qualified otherwise.
There is no additional premise on the base, the represented scheme or its
structure morphism. In particular, `CompactSpace` means quasi-compactness
without a Hausdorff assumption. Only the test schemes in the defining
universal family for `QuasiCompactOverBase` are required to be affine.

## Imports and retained definitions

The proof imports the published
`StructuralCompactnessSchemeCompatibilityStatement` and
`StructuralAtlasSchemeCompatibilityProof` by Lean name. Their transitive
imports supply `StructuralCompactness`, `SpaceBaseChange`, the actual
scheme embedding, scheme pullbacks, and Mathlib's scheme quasi-compactness
results. This proof adds a new Lean/Markdown pair and changes none of those
published files.

`IsQuasiCompact X` requires a scheme `W : Over S` and an actual
transformation `a : (schemeYoneda S).obj W ⟶ X.presheaf` with `IsEtale a`,
`IsSurjective a` and `CompactSpace W.left`. The atlas predicates retain
their geometric represented-pullback meanings. In particular, surjectivity
is geometric surjectivity of scheme morphisms, rather than surjectivity on
every set of sections.

`QuasiCompactOverBase X` tests `IsQuasiCompact (baseChange g X)` for every
affine `T : Scheme.{u}` and every `g : T ⟶ S`. The construction
`baseChange` and every affine test are used unchanged.
`FiniteTypeOverBase X` is the existing conjunction
`LocallyOfFiniteTypeOverBase X ∧ QuasiCompactOverBase X`.

## Implemented proof

`isQuasiCompact_schemeToSpace_iff U` proves the absolute comparison. In
the forward direction, `IsQuasiCompact.exists_atlas` supplies
`W, a, ha, hs, hW`. Since the presheaf of the embedded `U` is its scheme
Yoneda presheaf, the published
`exists_etale_surjective_of_represented_atlas a ha hs` gives a morphism
`f : W ⟶ U` over `S` whose underlying scheme map `f.left` is etale and
surjective. Its continuity and surjectivity, together with `hW`, give
`CompactSpace U.left` by Mathlib's
`Function.Surjective.compactSpace`. This step uses no quasi-compactness
condition on the atlas morphism. Conversely, `CompactSpace U.left`
allows the published identity-atlas lemma `IsQuasiCompact.of_scheme U`.

`quasiCompactOverBase_schemeToSpace_iff U` proves the structural
comparison in two directions.

Given structural quasi-compactness, the proof uses Mathlib's
`quasiCompact_iff_forall_isAffineOpen` to reduce the goal to compactness
of the inverse image of each affine open `V : S.Opens`. The open
subscheme `V` is an affine test scheme. Applying the structural hypothesis
to `V.ι : V ⟶ S` gives compactness of the corresponding space base
change. The existing isomorphism

```lean
baseChangeSchemeIso V.ι U :
  (schemeToSpace V).obj ((Over.pullback V.ι).obj U) ≅
    baseChange V.ι ((schemeToSpace S).obj U)
```

is sent to an isomorphism of whole presheaves by
`(forgetToPresheaf V).mapIso`. The published
`IsQuasiCompact.iff_of_iso` transports compactness back to the embedded
actual scheme pullback. The absolute comparison just proved gives
`CompactSpace (CategoryTheory.Limits.pullback U.hom V.ι : Scheme.{u})`.
Mathlib's `pullbackRestrictIsoRestrict U.hom V` identifies this pullback
with the open subscheme on `U.hom ⁻¹ᵁ V`. Applying continuous
surjective image compactness to the isomorphism's forward scheme map
gives compactness of that open subscheme.
`isCompact_iff_compactSpace` converts it to compactness of the inverse
image as a subset of `U.left`, as required by the affine-open criterion.

Conversely, assume `QuasiCompact U.hom` and take any affine test
`T` and any `g : T ⟶ S`. The actual scheme pullback of `U.hom` along
`g` is compact: Mathlib's instance uses quasi-compactness of its second
projection, obtained by scheme base change, and compactness of the
affine scheme `T`. `IsQuasiCompact.of_scheme` gives a compact identity
atlas for its embedded space. Transporting along the whole-presheaf
isomorphism induced by `baseChangeSchemeIso g U` gives the required
`IsQuasiCompact (baseChange g ((schemeToSpace S).obj U))`. Since `T`
and `g` were arbitrary, this proves the full structural predicate.

`finiteTypeOverBase_schemeToSpace_iff U` unfolds the existing finite
type conjunction by definitional equality. It uses `and_congr` with the
published `locallyOfFiniteTypeOverBase_schemeToSpace_iff U` and the
structural quasi-compactness comparison just proved. Its right side is
the explicit conjunction of local finite type and quasi-compactness of
`U.hom`.

Finally, `structuralCompactnessSchemeCompatibility` pairs these three
equivalences. Its declared type is precisely
`StructuralCompactnessSchemeCompatibilityStatement.{u}`.

## Provenance and original sources

This three-conjunct package is an internal derived compatibility theorem
for the Library definitions. The proof above combines published Library
interfaces with Mathlib's topological compactness, affine-open criterion
and actual scheme pullback results. It is not a transcription of a single
source proof.

The registered original source underlying the definitions is
`stacks-spaces-properties-morphisms-ed88ff78-2026-11-05`, retained in
`literature/Stacks Project - Properties of Algebraic Spaces and Morphisms
of Algebraic Spaces, full chapter PDFs (version ed88ff78)/`. The PDFs are
version `ed88ff78`, compiled 14 July 2026.

- *Properties of Algebraic Spaces*, Chapter 66, Definition 66.5.1
  ([Tag 03E3](https://stacks.math.columbia.edu/tag/03E3)) and Lemma
  66.5.2 ([Tag 03E4](https://stacks.math.columbia.edu/tag/03E4)),
  PDF/printed p.8, supply the compact-atlas definition and its
  topological motivation. The SHA-256 of `spaces-properties.pdf` is
  `7f71f8371bd2040b4cd3ec6171420ef6a1ce14f7a0a334d32c6d04821e1741bc`.
- *Morphisms of Algebraic Spaces*, Chapter 67, Lemma 67.8.1
  ([Tag 03HD](https://stacks.math.columbia.edu/tag/03HD)) and Definition
  67.8.2 ([Tag 03HE](https://stacks.math.columbia.edu/tag/03HE)), p.12,
  compare the representable and general quasi-compactness notions.
  Lemma 67.8.8 ([Tag 03KG](https://stacks.math.columbia.edu/tag/03KG)),
  pp.13–14, condition (3), gives the affine-test criterion used in the
  structural definition. Definition 67.23.1(3)
  ([Tag 03XF](https://stacks.math.columbia.edu/tag/03XF)) and Lemma
  67.23.4(6) ([Tag 040Y](https://stacks.math.columbia.edu/tag/040Y)),
  p.45, motivate the finite type conjunction and the existing local
  finite type atlas predicate. The SHA-256 of `spaces-morphisms.pdf` is
  `46497665981806a93d5b2f315314555ba457aaed3d967bf2d8f0cd4a2310e161`.

Worker 1640 read the source README and all pages cited here and checked
both PDF fingerprints. No source-specific errata file was found in the
checked workspace, project or pinned Library `notes/errata` locations.
The adjacent source text extractions are reading aids.

## Scope

The result proves represented-scheme compatibility for every scheme
base in universe `u`. It does not prove general algebraic-space
base-change stability or an intrinsic algebraic-space topology, nor a
comparison with `FiniteTypeOverRing`. Properness, Picard geometry and
the representability assemblies are outside this theorem.

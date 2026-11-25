# Smooth scheme atlases of the Picard stack over a finite-type `ℤ`-algebra: proof

Module: `Langlands.AlgebraicGeometry.Picard.FiniteTypePicardStackAtlasProof`.

The theorem `Langlands.AlgebraicGeometry.Picard.finiteTypePicardStackAtlas`
proves the published proposition
`Langlands.AlgebraicGeometry.Picard.FiniteTypePicardStackAtlasStatement.{u}`
at every universe `u`. Its type is exactly that proposition. The statement
module `Langlands.AlgebraicGeometry.Picard.FiniteTypePicardStackAtlasStatement`
and its Markdown are imported unchanged. The module contains only this
theorem. It adds no definition, lemma, hypothesis or axiom.

## What is proved

Let `R : Type u` be a commutative ring with `Algebra.FiniteType ℤ R`, and let
`X : Over (Spec (CommRingCat.of R))` have `IsProper X.hom` and
`Flat X.hom`. Then `PicardGroupoid.HasLocallyFiniteTypeSmoothSchemeAtlas X.hom`
holds. That is, there are a scheme `U` over `Spec R` with
`LocallyOfFiniteType U.hom` and an actual line bundle `L` on `U ×_R X` such
that, for every scheme `T` over `Spec R` and every actual line bundle `M` on
`T ×_R X`, the point-fibre presheaf `PicardGroupoid.pointFiberPresheaf X.hom L M`
on the full slice over `T.left` is represented by a scheme over `T.left` whose
structure map is smooth and surjective. The ring `R` may be non-reduced or
not a domain. `X` is any proper flat scheme over `Spec R`, with no
projectivity, smoothness, reducedness, connectedness, section,
global-functions or cohomological-flatness hypothesis. Test schemes `T` are
arbitrary.

## The implemented proof

The proof is one term:

```text
PicardGroupoid.finiteTypePicardStackAtlas_of_versalInputs
  finiteTypeFormalVersalBundle
  (versalAlgebraization_of_etaleApproximation
    CommutativeAlgebra.finiteTypeIntEtaleCompletionApproximation)
  picardOpennessOfVersality
```

It applies the published conditional theorem
`PicardGroupoid.finiteTypePicardStackAtlas_of_versalInputs` (module
`FiniteTypeVersalChartReduction`) to three published theorems that have no
hypotheses.

1. **Formal versality.** `finiteTypeFormalVersalBundle :
   FiniteTypeFormalVersalBundleStatement.{u}` (module
   `Langlands.AlgebraicGeometry.Picard.FiniteTypeFormalVersalBundleProof`).
   For every field `K` of finite type over `R` and every actual line bundle
   `L₀` on `Spec K ×_R X`, it gives a complete Noetherian local `R`-algebra
   `A` with a surjection `ε : A → K`, an actual line bundle on
   `Spec A ×_R X`, formally versal at the point `Spec ε`, whose pullback to
   `Spec K ×_R X` is isomorphic to `L₀`.
2. **Algebraization.** `versalAlgebraization_of_etaleApproximation`
   (module `Langlands.AlgebraicGeometry.Picard.VersalAlgebraizationReduction`)
   turns etale approximation into `VersalAlgebraizationStatement.{u}`. Its
   input is `CommutativeAlgebra.finiteTypeIntEtaleCompletionApproximation :
   CommutativeAlgebra.FiniteTypeIntEtaleCompletionApproximationStatement.{u}`
   (module `Langlands.CommutativeAlgebra.FiniteTypeIntEtaleCompletionApproximationProof`).
   That theorem is proved from the G-ring property of finite-type
   `ℤ`-algebras, Popescu factorization and etale approximation for smooth
   sources. Algebraization replaces the formal versal family over `Spec A` by
   an actual line bundle over a scheme `U` locally of finite type over
   `Spec R`, formally versal at a point `u₀` with residue field `K`, with
   residue bundle isomorphic to the pullback of the formal family along `Spec ε`.
3. **Openness of versality.** `picardOpennessOfVersality :
   PicardOpennessOfVersalityStatement.{u}` (module
   `Langlands.AlgebraicGeometry.Picard.PicardOpennessOfVersalityProof`). For
   a line bundle on `U ×_R X`, formally versal at a finite-type field point
   over `u₀`, there is an open neighbourhood of `u₀` such that the bundle is
   formally versal at every locally finite-type field point with image in
   it.

Inside `finiteTypePicardStackAtlas_of_versalInputs` the three inputs pass
through these published reductions:

- `finiteTypeVersalChart_of_formalVersal` (module
  `FiniteTypeVersalChartReduction`) combines (1) and (2) into
  `FiniteTypeVersalChartStatement.{u}`. This gives a versal chart locally of
  finite type through every finite-type field point, with prescribed residue
  bundle.
- `versalSmoothNeighbourhood_of_openness` (module
  `VersalSmoothNeighbourhoodOfOpenness`) turns (3) into
  `VersalSmoothNeighbourhoodStatement.{u}`. Every versal point has an open
  neighbourhood on which the restricted bundle has smooth point fibres.
- `finiteTypePointSmoothChart_of_versal` (module
  `FiniteTypePointSmoothChartReduction`) shrinks each versal chart to such a
  neighbourhood. This gives `FiniteTypePointSmoothChartStatement.{u}`: for
  every finite-type field point and every line bundle on its fibre, a chart
  locally of finite type over `Spec R` with smooth point fibres, and a point
  realizing that line bundle.
- `finiteTypePicardStackAtlas_of_pointSmoothCharts` (module
  `FiniteTypePicardStackAtlasAssembly`) takes the disjoint union of these
  charts over a `Type u` index of presented fields and unit-cohomology
  classes. It checks smoothness of the glued point fibres, then checks
  surjectivity on finite-type affine tests at closed points, using the
  Jacobson property of finite-type `ℤ`-algebras. This gives
  `FiniteTypePicardStackAtlasStatement.{u}`.

Finite presentation of `X.hom` is not assumed anywhere. The reductions
derive it from properness over the Noetherian base `Spec R`, since `R` is of
finite type over `ℤ`.

## Relation to the source

The Stacks Project, registered as
`stacks-artin-axioms-approximation-2026-11-06`, `artin.pdf` (Chapter 98
"Artin's Axioms"). The route follows Lemma 98.17.1 (Tag 07Y4), which builds a
smooth atlas as a disjoint union of smooth charts. Those charts come from
Lemma 98.13.8 (Tag 07XY), which algebraizes a versal formal object by
Lemma 98.12.7 (Tag 07XH) and then shrinks by openness of versality. The
target statement is the smooth surjective scheme atlas of Definition 94.12.1
for the Picard stack (Section 95.16), as in Proposition 99.10.2 of the
snapshot `stacks-picard-stack-algebraicity-2026-11-01`. It is restricted to
line bundles over a finite-type `ℤ`-algebra. The source proves that
proposition through the stack of coherent sheaves. The Lean proof instead
checks the versality, algebraization and openness inputs directly for line
bundles. The module documentation of each
reduction listed above records how its formal version differs from the
corresponding step in the source.

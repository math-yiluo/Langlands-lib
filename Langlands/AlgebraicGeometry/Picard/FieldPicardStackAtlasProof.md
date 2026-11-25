# Smooth scheme atlases of the Picard stack over a field: proof

Module: `Langlands.AlgebraicGeometry.Picard.FieldPicardStackAtlasProof`.

The theorem `Langlands.AlgebraicGeometry.Picard.fieldPicardStackAtlas`
proves the published proposition
`Langlands.AlgebraicGeometry.Picard.FieldPicardStackAtlasStatement.{u}`
at every universe `u`. Its type is exactly that proposition. The statement
module `Langlands.AlgebraicGeometry.Picard.FieldPicardStackAtlasStatement`
and its Markdown are imported unchanged. The module contains only this
theorem and adds no definition, lemma, hypothesis or axiom. The kernel
reports only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`.

## What is proved

Let `k : Type u` be any field, including an imperfect one, and let
`X : Over (Spec (CommRingCat.of k))` satisfy `IsProper X.hom`. Then
`PicardGroupoid.HasLocallyFiniteTypeSmoothSchemeAtlas X.hom` holds. That is,
there are a scheme `U` over `Spec k` with `LocallyOfFiniteType U.hom` and an
actual line bundle `L` on `U ×_k X` with the following property. For every
scheme `T` over `Spec k` and every actual line bundle `M` on `T ×_k X`, the
full point-fibre presheaf `PicardGroupoid.pointFiberPresheaf X.hom L M` on the
slice over `T.left` is naturally isomorphic to the lifted Yoneda presheaf of a
scheme `P` over `T.left`, and `P → T.left` is smooth and surjective.

The only hypothesis is properness. No projectivity, smoothness, reducedness,
connectedness, rational point, section, condition on global functions,
universal bundle or Picard-sheaf representability is assumed. The test
schemes `T` are arbitrary, and the representing objects are schemes.

## The implemented proof

The proof is one term:

```text
fieldPicardStackAtlas_of_finiteType
  (PicardGroupoid.finiteTypePicardStackAtlas_of_versalInputs
    finiteTypeFormalVersalBundle
    (versalAlgebraization_of_etaleApproximation
      CommutativeAlgebra.finiteTypeIntEtaleCompletionApproximation)
    picardOpennessOfVersality)
```

Every name in it is a published Library theorem. The term combines them as
follows.

### Step 1: the finite-type base case

The inner term proves `FiniteTypePicardStackAtlasStatement.{u}`. For every
commutative ring `R : Type u` of finite type over `ℤ` and every proper flat
`X₀` over `Spec R`, it gives the same kind of smooth surjective scheme atlas,
locally of finite type over `Spec R`. It applies the published reduction
`PicardGroupoid.finiteTypePicardStackAtlas_of_versalInputs` (module
`Langlands.AlgebraicGeometry.Picard.FiniteTypeVersalChartReduction`) to three
published theorems that have no hypotheses.

1. **Formal versality.** `finiteTypeFormalVersalBundle :
   FiniteTypeFormalVersalBundleStatement.{u}` (module
   `Langlands.AlgebraicGeometry.Picard.FiniteTypeFormalVersalBundleProof`).
   At every finite-type field point, it gives a formally versal actual line
   bundle over a complete Noetherian local `R`-algebra.
2. **Algebraization.** `versalAlgebraization_of_etaleApproximation` (module
   `Langlands.AlgebraicGeometry.Picard.VersalAlgebraizationReduction`) proves
   `VersalAlgebraizationStatement.{u}` from etale completion approximation.
   It receives
   `CommutativeAlgebra.finiteTypeIntEtaleCompletionApproximation :
   CommutativeAlgebra.FiniteTypeIntEtaleCompletionApproximationStatement.{u}`
   (module
   `Langlands.CommutativeAlgebra.FiniteTypeIntEtaleCompletionApproximationProof`).
   That theorem comes from the G-ring property of finite-type `ℤ`-algebras,
   Popescu factorization and etale approximation for smooth sources. As a
   result, the formal versal family is replaced by an actual line bundle over a
   scheme locally of finite type over `Spec R` that is formally versal at a
   point with the given residue field and residue bundle.
3. **Openness of versality.** `picardOpennessOfVersality :
   PicardOpennessOfVersalityStatement.{u}` (module
   `Langlands.AlgebraicGeometry.Picard.PicardOpennessOfVersalityProof`).
   Formal versality at one finite-type field point extends to every locally
   finite-type field point of some open neighbourhood.

Inside the reduction, these inputs first give versal charts and then smooth
charts through every finite-type field point
(`finiteTypeVersalChart_of_formalVersal`,
`versalSmoothNeighbourhood_of_openness` and
`finiteTypePointSmoothChart_of_versal`). Finally,
`finiteTypePicardStackAtlas_of_pointSmoothCharts` (module
`FiniteTypePicardStackAtlasAssembly`) takes the disjoint union of these
charts and checks surjectivity at closed points, using the Jacobson property.

### Step 2: from finite-type `ℤ`-algebras to fields

The outer term `fieldPicardStackAtlas_of_finiteType` (module
`Langlands.AlgebraicGeometry.Picard.FieldPicardStackAtlasReduction`) turns
`FiniteTypePicardStackAtlasStatement.{u}` into the target. Given `k` and a
proper `X`, it works in three steps.

- `field_hasProperFlatFiniteTypeModel` (module
  `Picard.ProperFlatFiniteTypeModel`) gives a ring `R : Type u` of finite type
  over `ℤ` with a map `R → k`, a proper flat `p₀ : X₀ ⟶ Spec R`, and a
  Cartesian square that exhibits `X.hom` as the base change of `p₀` along
  `Spec k → Spec R`. Flatness and local finite presentation of `X.hom` are
  derived there from Mathlib instances, not assumed: every morphism to the
  spectrum of a field is flat, and a morphism locally of finite type to a
  locally noetherian scheme is locally of finite presentation. Properness and
  flatness of the model then descend by noetherian approximation.
- Step 1, applied to `R` and `Over.mk p₀`, gives an atlas for `p₀`.
- `PicardGroupoid.hasLocallyFiniteTypeSmoothSchemeAtlas_of_isPullback` (module
  `Picard.StackAtlasBaseChange`) base changes that atlas along the Cartesian
  square. The chart becomes the pullback of `U₀` to `Spec k`, which is still
  locally of finite type. Each point fibre over `Spec k` is naturally
  isomorphic to a point fibre of the model. So the model's smooth surjective
  representing schemes also represent the point fibres over `Spec k`.

## Relation to the source

The target is the field case of The Stacks Project, snapshot
`stacks-picard-stack-algebraicity-2026-11-01`, `0D04.html`,
Proposition 99.10.2: the Picard stack of a flat, proper, finitely presented
morphism is algebraic. It is stated with the smooth surjective scheme atlas
of `026O.html`, Definition 94.12.1, and with scheme point fibres, as the
statement Markdown explains. The source proves that proposition through the
stack of coherent sheaves.

The Lean proof follows a different route. It passes to a noetherian model
over a finite-type `ℤ`-algebra, where it builds the atlas with Artin's
criteria for line bundles. These criteria are formal versality,
algebraization and openness of versality, as in the Stacks Project chapter
"Artin's Axioms" (Lemma 98.17.1, Tag 07Y4, and Lemma 98.13.8, Tag 07XY).
The proof then base changes that atlas to `k`. The Markdown of each module
listed above records how its formal version differs from the corresponding
source step. This proof module adds no new mathematics; it only composes
those published results.

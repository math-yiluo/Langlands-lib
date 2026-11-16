# Full rigidified Picard representability over a field: proof

Author: Worker 943.

`Langlands.AbelianScheme.fieldRigidifiedPicardRepresentability.{u}`, in module
`Langlands.AlgebraicGeometry.Picard.FieldRigidifiedPicardRepresentabilityProof`,
proves the unchanged statement
`Langlands.AbelianScheme.FieldRigidifiedPicardRepresentabilityStatement.{u}`
for every universe `u`. For every field `k : Type u` and every abelian scheme
`A` over `Spec k`, it gives an actual `P : Over (Spec k)` and an actual
rigidified family `L : RigidifiedFamily A P`. The structure morphism
`P.hom` is locally of finite type (`LocallyOfFiniteType P.hom`), and `L`
satisfies
`RigidifiedLineBundle.IsUniversal A.X.hom (unitSection A) (unitSection_comp A) L`.
The field `k` is arbitrary (imperfect fields included). No hypothesis is
added.

## Published inputs

The proof is a single application of a published conditional reduction to
two published proofs.

| Library theorem | Module | Content |
| --- | --- | --- |
| `Langlands.AbelianScheme.fieldRigidifiedPicardRepresentability_of_formalVersal_of_etaleApproximation` | `Langlands.AlgebraicGeometry.Picard.FieldRigidifiedPicardRepresentabilityReduction` | `FiniteTypeFormalVersalBundleStatement.{u}` and `FiniteTypeIntEtaleCompletionApproximationStatement.{u}` together imply the target. |
| `Langlands.AlgebraicGeometry.Picard.finiteTypeFormalVersalBundle` | `Langlands.AlgebraicGeometry.Picard.FiniteTypeFormalVersalBundleProof` | Proves `FiniteTypeFormalVersalBundleStatement.{u}`: every line bundle on a finite-type field fibre of a proper flat scheme over a finite-type `ℤ`-algebra is the closed fibre of a line bundle over a complete Noetherian local base, formally versal at the closed point. |
| `Langlands.CommutativeAlgebra.finiteTypeIntEtaleCompletionApproximation` | `Langlands.CommutativeAlgebra.FiniteTypeIntEtaleCompletionApproximationProof` | Proves `FiniteTypeIntEtaleCompletionApproximationStatement.{u}`: every maximal localization of a finite-type `ℤ`-algebra has finite-order approximation in étale neighbourhoods for maps into its completion. |

## Proof

The theorem is the term

```
fieldRigidifiedPicardRepresentability_of_formalVersal_of_etaleApproximation
  finiteTypeFormalVersalBundle finiteTypeIntEtaleCompletionApproximation
```

at universe `u`. The reduction it applies (see the paired Markdown of
`FieldRigidifiedPicardRepresentabilityReduction`) does the following.

1. `versalAlgebraization_of_etaleApproximation` turns étale approximation
   into algebraization of formally versal families
   (`VersalAlgebraizationStatement`).
2. `PicardGroupoid.finiteTypePicardStackAtlas_of_versalInputs` combines
   formal versality, algebraization and the published openness of
   versality `picardOpennessOfVersality`. The result is a smooth scheme
   atlas of the actual Picard stack over finite-type `ℤ`-algebras
   (`FiniteTypePicardStackAtlasStatement`).
3. `fieldPicardStackAtlas_of_finiteType` and
   `fieldPicardSheafRepresentability_of_stackAtlas` pass to fields. They
   show that the fppf Picard sheaf of every proper scheme over a field is
   represented by a separated scheme locally of finite type.
4. `fieldRigidifiedPicardRepresentability_of_fieldPicardSheaf` specializes
   this to the abelian scheme `A`. It uses the published
   `smoothProperConnectedGlobalFunctions`, `rigidifiedFppfComparison`,
   `RelativePicard.forgetSheafIso` and
   `RigidifiedLineBundle.representationUniversalBundle` to obtain the
   universal rigidified bundle on the representing scheme.

The theorem depends only on the standard axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Provenance

This is an internal composition of published Library results; it makes no
new mathematical assertion. The mathematical route is the one recorded in
Edixhoven, van der Geer and Moonen, *Abelian Varieties* (preliminary
draft), §(6.2)–(6.3)(iii). There, representability of the Picard functor of
a proper scheme over a field by a scheme locally of finite type (due to
Murre and Oort) gives the rigidified Picard scheme of an abelian variety.
The Library proves that representability through Artin's axioms
(formal versality, algebraization via étale approximation and Popescu's
theorem, and openness of versality).

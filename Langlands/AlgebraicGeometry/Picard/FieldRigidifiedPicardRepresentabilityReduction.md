# Reductions of field rigidified Picard representability

Author: Worker 943.

This internal assembly shows how the open target
`Langlands.AbelianScheme.FieldRigidifiedPicardRepresentabilityStatement.{u}`
follows from published Library results, given one of several
still-unproved upstream propositions. That target says: for every field
`k : Type u` and every abelian scheme `A` over `Spec k`, there are an actual
`P : Over (Spec k)` and an actual rigidified family
`L : RigidifiedFamily A P` with `LocallyOfFiniteType P.hom` and
`RigidifiedLineBundle.IsUniversal A.X.hom (unitSection A) (unitSection_comp A) L`.

Every declaration in this module keeps its upstream input as an explicit
hypothesis. The module proves none of those inputs, and it is **not** a
proof of `FieldRigidifiedPicardRepresentabilityStatement`.

## Declarations

All declarations live in namespace `Langlands.AbelianScheme`, in module
`Langlands.AlgebraicGeometry.Picard.FieldRigidifiedPicardRepresentabilityReduction`.

### From the pointed smooth-proper statement

`fieldRigidifiedPicardRepresentability_of_smoothProper` derives the target
from `SmoothProperRigidifiedPicardRepresentabilityStatement.{u}`. That
statement is about a smooth, proper, geometrically connected scheme over a
field with a section. Given `k` and `A`, the proof applies it to `A.X`
(the instances `Smooth`, `IsProper` and `GeometricallyConnected` of the
structure morphism come from the `AbelianScheme` structure), with the
section `unitSection A` and its equation `unitSection_comp A`. It then drops
the extra separatedness conclusion. `RigidifiedFamily A P` is by definition
the rigidified relative family for `A.X.hom` and the unit section, so the
parameter and bundle are passed on unchanged.

### From the representable fppf Picard sheaf

`fieldRigidifiedPicardRepresentability_of_fieldPicardSheaf` derives the
target from `FieldPicardSheafRepresentabilityStatement.{u}`. That
statement says the actual fppf Picard sheaf
`RelativePicard.classSheafPresheaf X.hom` of every proper scheme over a
field is represented by a scheme over `Spec k` that is separated and
locally of finite type. For `k` and `A`, the proof works as follows.

1. Apply the hypothesis to the proper scheme `A.X`. This gives `P`, local
   finite type `hlft`, and a representation `r` of the Picard-sheaf
   presheaf.
2. Prove that the universal structure-sheaf condition holds for
   `A.X.hom`. For every test object `T` over `Spec k` and every open `U` of
   `T.left`, the component of `relativeProjection A.X.hom` at `T` and `U` is
   an isomorphism. This uses the published theorem
   `Langlands.AlgebraicGeometry.smoothProperConnectedGlobalFunctions`
   (module `SmoothProperConnectedGlobalFunctionsProof`). It is applied to
   the base change `pullback.fst T.hom A.X.hom`, which is smooth, proper and
   geometrically connected because these properties are stable under base
   change.
3. Apply the published theorem `rigidifiedFppfComparison` (module
   `RigidifiedFppfComparisonProof`) to `A.X.hom`, which is quasi-compact and
   quasi-separated, together with the unit section and step 2. This shows
   that the canonical map
   `RigidifiedLineBundle.toPicardSheaf A.X.hom (unitSection A) (unitSection_comp A)`
   from the rigidified class presheaf to the Picard sheaf is an
   isomorphism.
4. Compose that isomorphism with the published natural isomorphism
   `RelativePicard.forgetSheafIso A.X.hom`. Transporting `r` along the
   inverse of the composite with `RepresentableBy.ofIso` gives a
   representation, by the same `P`, of the rigidified class presheaf built
   from the published coherence proof
   `Langlands.SchemeModule.RigidifiedModule.pullbackCoherence`.
5. Apply the published theorem
   `RigidifiedLineBundle.representationUniversalBundle` (module
   `RigidifiedRepresentationUniversalBundleProof`). It turns that
   representation into an actual rigidified bundle `L` on `P` that
   satisfies `RigidifiedLineBundle.IsUniversal`. The result is `⟨P, L, hlft, hL⟩`.

### Further upstream inputs

The next four theorems compose the theorem above with conditional
reductions that are already published. Each one replaces the hypothesis by
an input further upstream.

- `fieldRigidifiedPicardRepresentability_of_stackAtlas` takes
  `FieldPicardStackAtlasStatement.{u}` (a smooth scheme atlas of the actual
  Picard stack of proper schemes over fields). It uses the published
  `fieldPicardSheafRepresentability_of_stackAtlas` (module
  `FieldPicardSheafRepresentabilityReduction`).
- `fieldRigidifiedPicardRepresentability_of_finiteTypeStackAtlas` takes
  `FiniteTypePicardStackAtlasStatement.{u}` (the same atlas for proper flat
  schemes over finite-type `ℤ`-algebras). It uses the published
  `fieldPicardStackAtlas_of_finiteType` (module
  `FieldPicardStackAtlasReduction`).
- `fieldRigidifiedPicardRepresentability_of_versalInputs` takes
  `FiniteTypeFormalVersalBundleStatement.{u}` (formally versal line bundles
  over complete Noetherian local bases) and
  `VersalAlgebraizationStatement.{u}` (algebraization of such families). It
  uses the published
  `PicardGroupoid.finiteTypePicardStackAtlas_of_versalInputs` (module
  `FiniteTypeVersalChartReduction`). That reduction's third input, openness
  of versality, is discharged by the published proof
  `picardOpennessOfVersality` (module `PicardOpennessOfVersalityProof`).
- `fieldRigidifiedPicardRepresentability_of_formalVersal_of_etaleApproximation`
  takes `FiniteTypeFormalVersalBundleStatement.{u}` and
  `Langlands.CommutativeAlgebra.FiniteTypeIntEtaleCompletionApproximationStatement.{u}`
  (finite-order approximation in étale neighbourhoods over finite-type
  `ℤ`-algebras). The algebraization input is replaced through the published
  `versalAlgebraization_of_etaleApproximation` (module
  `VersalAlgebraizationReduction`).

### Packaging definition

`fieldRigidifiedPicardRepresentabilityOfFieldPicardSheaf` is the term of type
`FieldPicardSheafRepresentabilityStatement.{u} → FieldRigidifiedPicardRepresentabilityStatement.{u}`
given by `fieldRigidifiedPicardRepresentability_of_fieldPicardSheaf`. It is a
`def` (with the `defProp` linter disabled locally), so the implication can be
named as a single definition declaration, as the other published
reductions in this directory do. It has no other content.

## Scope

The field `k` is arbitrary, including imperfect fields, as are the abelian
scheme `A` and the universe `u`. The conclusions are exactly the target's:
universality concerns every test scheme over `Spec k`, including
nonreduced, empty and non-quasi-compact ones. No algebraic closure,
projectivity, positive dimension, coherence, comparison, existing dual
scheme (`HasDualScheme A`) or universal-bundle assumption is added. The
only assumptions are the named upstream hypotheses. The proofs use only the
standard axioms.

## Provenance and remaining obligations

No new external assertion is made. Every step is a published Library result
cited above by its Lean name, so the provenance is an internal composition.
The mathematics is the source's. Edixhoven, van der Geer and Moonen,
*Abelian Varieties* (preliminary draft, source id
`edixhoven-vandergeer-moonen-abelian-varieties-draft`), §(6.2) (printed
pp. 88–89) identifies the rigidified functor with the Picard functor when
the structure sheaf is universally pushed forward and a section exists.
§(6.3)(iii) (printed p. 89) gives representability by a scheme locally of
finite type for a proper scheme over a field, citing Murre and Oort. The
proof of that representability is exactly what the hypotheses still
supply.

The open inputs belong to separate proof tasks. In the shortest chain they
are `FiniteTypeFormalVersalBundleStatement` (task
`72b6bcbb-1ed4-456e-a4d3-aadbfdc6fe56`) and
`FiniteTypeIntEtaleCompletionApproximationStatement` (task
`1df3798f-6ffd-4432-908f-8266a6b374fb`). Once published proofs of both
exist, applying
`fieldRigidifiedPicardRepresentability_of_formalVersal_of_etaleApproximation`
proves the target. A published proof of any one of
`FieldPicardSheafRepresentabilityStatement`, `FieldPicardStackAtlasStatement`
or `FiniteTypePicardStackAtlasStatement` would also prove it, through the
corresponding theorem above. Until then, this module does not prove the target.

# Arbitrary geometric inverse image and coefficient scalar extension

Let `f : Z ⟶ X` be any morphism of `Scheme.{u}` and let
`φ : R →+* S` be a homomorphism of commutative rings in `Type u`.
All module carriers remain in universe `u`. This internal construction
compares the two orders of actual geometric inverse image and actual
sheafified extension of coefficient scalars. It has no etale or affine
hypothesis on `f`, and no flatness or finiteness hypothesis on `φ`.

The imported constructions are the affine-Kan/sheafification inverse image
from `EtaleInverseImage`, its actual inverse/direct-image adjunction,
the geometric direct-image comparisons from `EtaleImageFunctoriality`,
and sectionwise scalar restriction and sheafified tensor extension from
`EtaleScalarRestriction` and `EtaleScalarExtension`.

## Strict interchange of the right adjoints

`directImageRestrictScalarsIso φ f` is the natural isomorphism

```text
directImage f (ModuleCat S) ⋙ sheafRestrictScalars φ X
  ≅ sheafRestrictScalars φ Z ⋙ directImage f (ModuleCat R).
```

Both sides evaluate a sheaf at the actual geometric pullback of each
small-etale test object and then restrict its section-module scalars. Their
object and morphism data are definitionally equal, so the comparison is
`Iso.refl`. This is a comparison of actual geometric direct image, rather
than a hypothesized base-change map.

`directImageId_restrictScalars` and `directImageComp_restrictScalars` show
that applying scalar restriction to the actual identity and composition
direct-image comparisons gives the corresponding comparison with
`R` coefficients. These are equalities of actual sheaf morphisms, proved
by the definitional equality of their underlying presheaf maps.

## Constructed composite adjunctions and their comparison

`extendScalarsInverseImageAdjunction φ f` composes the existing
scalar-extension/restriction adjunction over `X` with the existing
geometric inverse/direct-image adjunction with `S` coefficients. It
transports the right adjoint along the strict interchange above.

`inverseImageExtendScalarsAdjunction φ f` instead composes geometric inverse
image with `R` coefficients and scalar extension over `Z`. Both are actual
constructed adjunctions with the same right adjoint

```text
sheafRestrictScalars φ Z ⋙ directImage f (ModuleCat R).
```

Uniqueness of left adjoints therefore constructs the natural isomorphism
`inverseImageExtendScalarsIso φ f`:

```text
sheafExtendScalars φ X ⋙ inverseImage f S
  ≅ inverseImage f R ⋙ sheafExtendScalars φ Z.
```

Neither the comparison nor either adjunction is an input. This argument
does not require exactness of scalar extension and does not assert it.
The lemmas `inverseImageExtendScalarsIso_unit` and
`inverseImageExtendScalarsIso_counit` are the corresponding actual composite
unit and counit equations from `Adjunction.leftAdjointUniq`. They specify
the normalization of the constructed comparison by the supplied, already
constructed adjunctions.

## Natural coefficient maps

For a sheaf `F` with `R` coefficients,
`inverseImageScalarUnit φ f F` is the morphism

```text
(inverseImage f R).obj F
  ⟶ (sheafRestrictScalars φ Z).obj
       ((inverseImage f S).obj ((sheafExtendScalars φ X).obj F)).
```

It is the scalar-extension unit on the pulled-back `R`-sheaf, followed by
scalar restriction of the inverse comparison. The lemma
`inverseImageScalarUnit_homEquiv` identifies it as the actual scalar
adjunction image of that inverse comparison. This records its universal
meaning, rather than only its type.
`inverseImageScalarUnitNat` packages these maps as a natural transformation
in `F`. Its naturality proof uses naturality of the scalar unit and of the
constructed comparison.

The earlier `EtaleScalarExtensionPullback` compares scalar extension with
etale restriction by sheafification compatibility. The present comparison
uses the general inverse image. Agreement with that older etale comparison,
full inverse-image/scalar coherence, and the separate inverse-image/scalar
restriction comparison are further obligations. No coefficient-extension
comparison for cohomology, support functors, smooth actions or Harris
specialization is inferred here.

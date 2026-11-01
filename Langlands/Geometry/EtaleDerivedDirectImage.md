# Higher and bounded-below derived geometric direct images

Let `f : Z ⟶ X` be any morphism of `Scheme.{u}` and let `R : Type u` be a
commutative ring. Coefficients are the actual sheaves with values in
`ModuleCat.{u} R` on the small-etale sites. This internal construction
specializes the existing resolution and derived-category machinery to
the previously constructed geometric direct image. It does not assume
cohomology sheaves, resolutions or comparisons as input data.

## Left exactness and injectives

Write `D = EtaleDirectImage.directImage f (ModuleCat R)`.
The actual inverse/direct-image adjunction proves that `D` preserves
limits of shapes in universe `u`; finite-limit preservation in arbitrary
finite diagram universes follows. The previously proved exactness of
the constructed inverse image shows that the left adjoint preserves
monomorphisms. Mathlib's injective-preservation theorem for right adjoints
therefore proves `directImage_preservesInjectives`.

No exactness of `D` is asserted. An arbitrary inverse image is not claimed
to preserve injective objects.

## Actual resolution complexes and higher direct images

For a coefficient sheaf `F` on `Z`, `resolutionComplex f R F` applies `D`
termwise to the chosen actual injective resolution of `F`. The theorem
`resolutionComplex_injective` proves each resulting term injective.
This is an image complex computing a derived functor; it is not generally
an injective resolution of the ordinary sheaf `D.obj F`.

`homotopyDirectImage` is the actual right-derived functor to the homotopy
category of nonnegative cochain complexes of module sheaves on `X`.
`higherDirectImage f R q` is `D.rightDerived q`, with `q : ℕ`.
The sheaf categories and their enough-injectives structures come from
the existing Mathlib small-etale construction.
`resolutionComplexIso` and `higherDirectImageIso` identify the constructed
object and its cohomology with the image of the chosen resolution.
`higherDirectImageZeroIso` identifies degree zero naturally with the same
geometric direct-image functor, using its proved finite-limit preservation.

## Global sections and geometric base change of the terminal object

Geometric pullback of small-etale objects preserves terminal objects.
The actual isomorphism

```text
PreservesTerminal.iso (etaleObjectPullback f) :
  (etaleObjectPullback f).obj (terminal of X.Etale)
    ≅ terminal of Z.Etale
```

therefore identifies evaluation of a direct-image sheaf at the terminal
object on `X` with evaluation of the original sheaf at the terminal object
on `Z`. `terminalSectionsIso` uses the contravariant sheaf map along this
isomorphism, with the opposite and inverse in the required directions.
Its naturality is exactly naturality of the underlying sheaf morphism.
Combining this with the existing terminal-evaluation descriptions of
global sections constructs

```text
directImageSectionsIso f R :
  D ⋙ EtaleDerivedSections.sections X R
    ≅ EtaleDerivedSections.sections Z R.
```

`compositeSectionsRightDerivedIso` derives this actual natural
isomorphism, using `NatTrans.rightDerived` on its forward and inverse
maps. Their inverse laws follow from the proved identity and composition
laws for derived natural transformations. It identifies the right
derived functor of the composite `D ⋙ sections X R` with ordinary
cohomology on `Z`. This is not an interchange of sections with individual
higher direct images and is not a Grothendieck spectral sequence.

## Bounded-below derived direct image

Assume independently specified `HasDerivedCategory` instances for the
module-sheaf categories on `Z` and `X`, in universes `wZ` and `wX`.
`rightDerivedFunctor` is the actual functor

```text
DerivedCategory.Plus (ModuleSheaf Z R)
  ⥤ DerivedCategory.Plus (ModuleSheaf X R)
```

given by `D.rightDerivedFunctorPlus`.
`derivedDirectImage` places a sheaf in degree zero and applies that actual
derived functor through the existing `DerivedPlus.derivedComplex`
construction. `complex` is the integer-indexed bounded-below direct-image
complex obtained from the chosen injective resolution.
`resolutionIso` shows that every actual injective resolution on `Z`
computes the same derived-image object. `complexIso` is the specialization
to the chosen resolution.

`complexMap` is the termwise image of a chosen compatible lift of a
coefficient morphism between the chosen resolutions. These chosen
complex maps are not asserted strictly functorial. The
`resolutionIso_hom_naturality` equation for every compatible resolution
map and its `complexIso_hom_naturality` specialization identify the
localized complex map with the actual functorial derived-image map.
Their proofs use the already proved generic
`DerivedPlus.derivedComplexIso_hom_naturality`.

`homologyNatIso` recovers the higher-direct-image functor naturally from
nonnegative cohomology of `derivedDirectImage`.
`homologyZeroIso` recovers actual geometric direct image in degree zero,
and `isZero_homology_of_neg` proves negative cohomology vanishes for these
derived images of sheaves. `diagramFunctor` applies the same actual
functor to every object and arrow of an arbitrary coefficient diagram,
whose index category has independent object and morphism universes.

The module does not construct a derived inverse/direct-image adjunction,
composition or base-change comparison for derived direct image,
Grothendieck spectral sequence, compact supports, smooth actions or the
Harris specialization. In particular the resolution argument does not
extend the earlier etale pullback construction by incorrectly assuming
that arbitrary inverse image preserves injectives.

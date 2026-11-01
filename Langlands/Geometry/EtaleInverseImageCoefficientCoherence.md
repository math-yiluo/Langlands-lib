# Coefficient-ring coherence of arbitrary inverse-image scalar extension

Let `f : Z ⟶ X` be an arbitrary morphism of `Scheme.{u}`. Let
`R`, `S`, `T : Type u` be commutative rings and let
`φ : R →+* S` and `ψ : S →+* T`. Module carriers remain in universe `u`.
This internal construction proves identity and composition compatibility in
the coefficient ring map for the actual comparison from
`EtaleInverseImageScalars`. It uses the existing coefficient identity and
composition isomorphisms from `EtaleScalarExtensionCoherence`.
There is no etale, affine, flatness or finiteness hypothesis.

## Coefficient identity

`inverseImageExtendScalarsIso_ringId` proves that interchange for the ring
identity agrees with removal of the actual identity scalar extensions on
either side of inverse image. It is an equality of natural transformations
from `sheafExtendScalars (RingHom.id R) X ⋙ inverseImage f R` to
`inverseImage f R`. The two actual functor unitors appear explicitly.

The proof applies injectivity of adjunction conjugation with respect to the
actual scalar/geometric adjunctions. The public scalar conjugate formula
from `EtaleInverseImageScalarCoherence`, the existing conjugate formula for
`sheafExtendScalarsIdIso`, and Mathlib's whiskering and unitor formulas
reduce the equation to scalar restriction of actual section modules.
Both resulting presheaf maps are the same, which proves the equation.

## Coefficient composition

`inverseImageExtendScalarsIso_ringComp` proves equality of the following
routes from
`sheafExtendScalars (ψ.comp φ) X ⋙ inverseImage f T` to
`inverseImage f R ⋙ (sheafExtendScalars φ Z ⋙ sheafExtendScalars ψ Z)`:

1. Interchange inverse image with extension by `ψ.comp φ`, then split the
   coefficient extension over `Z`.
2. Split coefficient extension over `X`, interchange inverse image first
   with extension by `ψ` and then with extension by `φ`, and regroup the
   functors.

The equality includes each actual functor associator, including the inverse
associator between the two successive interchanges.

The proof again applies conjugation injectivity for the actual composite
adjunctions. Mathlib's composition, whiskering and associator formulas,
the computed scalar-interchange conjugates, and the existing formula
`conjugate_sheafExtendScalarsCompIso_hom` reduce both routes to the same
actual scalar-restriction comparison on each section. The private inverse
associator helper is obtained by taking inverses of Mathlib's proved
conjugate-isomorphism equality for the forward associator.
The remaining presheaf maps agree definitionally.
No coefficient or geometric compatibility equation is an input.

## Actual composite-coefficient comparison

`inverseImageCompositeScalarsIso f φ ψ` constructs the first route as a
natural isomorphism with the source and target displayed above.
`inverseImageCompositeScalarsIso_eq` proves it equals the second route as an
actual natural isomorphism, by extensionality and the proved composition
equation.

Together with `EtaleInverseImageScalarCoherence`, these results give the
geometric and coefficient identity and composition laws for this scalar
extension comparison. Agreement with the older etale-restriction
comparison and the separate inverse-image/scalar-restriction comparison
remain further obligations. No scalar-extension exactness,
cohomology base-change, support, smooth-action or Harris specialization is
asserted.

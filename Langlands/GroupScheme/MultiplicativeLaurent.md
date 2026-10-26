# Relative Laurent coordinates for the actual multiplicative group

Author: Worker 487.

This module constructs `Gm.relativeLaurentIso R`, an isomorphism in
`Over (Spec R)` from the underlying scheme of the published
`Langlands.GroupScheme.Gm (Spec R)` to `Spec (LaurentPolynomial R)` with its
coefficient structural map. Here `R : CommRingCat` is arbitrary, including the
zero ring; an ordinary commutative ring is supplied as `CommRingCat.of R`.
All declarations below are in `Langlands.GroupScheme.Gm`.

## Internal provenance

This is an internal universal-property construction from the published
`Langlands.GroupScheme.Multiplicative` module and Mathlib's
`LaurentPolynomial.eval₂`, `AddMonoidAlgebra.ringHom_ext`, and
`Functor.RepresentableBy.uniqueUpToIso`. It introduces no external literature
claim. The existing `Gm` remains the pullback of the integral Laurent spectrum.
The new isomorphism is proved by natural representability on every test scheme,
using the existing `Gm.representableBy`; no comparison isomorphism or pointwise
geometric identification is assumed.

## The relative spectrum and its universal property

`relativeCoordUnit R` is the unit with value `T 1` and inverse `T (-1)`.
`relativeCoordUnit_zpow_val` says that its integer power has value `T m`.
`specHomEquiv_specMap` records that postcomposing a map into a spectrum with
`Spec.map φ` precomposes its ring map on global sections with `φ`.

`relativeLaurent R` is exactly
`Over.mk (Spec.map (CommRingCat.ofHom LaurentPolynomial.C))`. Its structural map
therefore comes from the actual coefficient inclusion `R → LaurentPolynomial R`.

For `T : Over (Spec R)`, `relativeUnits T x` takes the image of the coordinate
unit under the ring map associated by `specHomEquiv` to `x.left`.
`relativeUnits_comp` states its naturality under precomposition: global units
are pulled back by `Units.map` of the map on global sections.

Conversely, `relativeLift T a` evaluates Laurent polynomials using the coefficient
map associated to `T.hom` and the given global unit `a`. The coefficient identity
`eval₂_C` proves that this is a morphism over `Spec R`.
`relativeUnits_relativeLift` follows by evaluating `T 1`.
`relativeLift_relativeUnits` uses Laurent ring-map extensionality: coefficient
maps agree because the original map is over `Spec R`, and every `T m` is an
integer power of the coordinate unit. These two identities give
`relativeHomEquiv T : (T ⟶ relativeLaurent R) ≃ Γ(T.left, ⊤)ˣ`.

`relativeRepresentableBy R` packages this equivalence and its naturality as a
representation of the same global-units functor already represented by `Gm`.
`relativeLaurentIso R` is the isomorphism obtained from uniqueness of these two
representations.

## Compatibility with the published points

`relativeHomEquiv_comp_relativeLaurentIso` says that for every test scheme `T`
and every `x : T ⟶ (Gm (Spec R)).X`, the global unit of
`x ≫ (relativeLaurentIso R).hom` is exactly `Gm.pointsEquiv (Spec R) T x`.
The proof uses the explicit Yoneda construction and naturality of the published
units equivalence.

For an affine test scheme `f : Spec A ⟶ Spec R`,
`relativeLaurentIso_affinePointsEquiv_val` states that the ring map associated
to `(x ≫ (relativeLaurentIso R).hom).left` sends `T 1`, after applying
`Scheme.ΓSpecIso A`, to the value of `Gm.affinePointsEquiv f x` in `A`.
Thus the relative Laurent coordinate evaluates to precisely the unit already
assigned by the existing `Gm` API.

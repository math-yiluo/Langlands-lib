# Root parametrizations under arbitrary coefficient base change

## Scope and provenance

This internal derived module extends the field-restricted interfaces in the
`RootBaseChange` section of `LocalSplitBigCellProof`, the `BaseChange` section of
`LocalWeylNormalizationStatement`, and the `WeylBaseChange` section of
`LocalSplitFieldPoints` to every commutative coefficient algebra. It imports the
published interfaces and leaves those files unchanged. There is no new literature
claim. All declarations lie in `Langlands.GroupScheme.LocalSplitRootBaseChange`.

Fix a commutative ring `R` and a commutative `R`-algebra `A`, in the same arbitrary
universe `u`. Write `p : Spec A → Spec R` for `algebraBaseMap R A`. Neither `R` nor
`A` is assumed local, reduced, noetherian, or a field. There is no restriction on
characteristic, and `A` may be the zero ring. The maps and identities use every
scheme over `Spec A`, including tests with nilpotents.

## Additive-group comparison

`gaCoordinates A Z` is the multiplicative encoding of the one additive coordinate
of a point of `p* Ga_R`. It is the composite of the pullback point equivalence
with the standard vector coordinates over `R`, viewing `Z` over `Spec R`.

`gaIso_naturality` compares these coordinates with the standard additive group
over `A`, naturally in `Z`. Pullback point naturality and the standard coordinate
pullback law give this equality directly. `gaIso A : p* Ga_R ≅ Ga_A` is constructed
from that natural equivalence of point groups by `isoOfPoints`. This construction
does not use the field-restricted natural-vector-coordinate predicate.
`coordinates_comp_gaIso_hom` records exactly the coordinate identity.

`baseChangePointsEquiv_scalarPoint` says that a standard point of `Ga_A` with
coordinate `c`, composed with the inverse of `gaIso A`, corresponds to the
standard `Ga_R` point with the same section `c`. Its proof applies the coordinate
identity and cancels the two directions of the isomorphism.

## Root maps and actual root subgroups

For any group scheme `G` over `Spec R` and homomorphism `u : Ga_R → G`, define

`baseChangeRoot A u = (gaIso A).inv ≫ (GroupScheme.baseChange p).map u`.

`baseChangePointsEquiv_rootPoint` identifies its value at any section `c` over
any test `Z` with the original root-map value over `Z` regarded as an `R`-scheme.
`baseChangePointsEquiv_orderedProduct` proves the corresponding identity for any
finite ordered list of supplied root maps, by preservation of products.

Fix a finite coordinate index `I`, a torus map `i : G_m^I → G`, and an integer
exponent character `m : I → ℤ`. `isRepresentedBy_baseChangeRoot` proves that if
`u` represents the actual relative root subgroup for `(i,m)`, the transported
root map represents that subgroup for the canonical base-changed torus map and
the same exponent vector. The proof uses base change of the represented
subgroup, transport by the split-torus base-change isomorphism, compatibility of
exponent characters, and the additive-group isomorphism. It transports the
entire subgroup functor, rather than only its field-valued points.

`baseChangePointsEquiv_torus` gives the corresponding point identity for `i`.
`charValue_exponentCharacter_baseChange` identifies the character value on every
torus point before and after the same transport.

`isRootParametrization_baseChangeRoot` combines these results to preserve all
three clauses of `LocalSplitCell.IsRootParametrization`: representation of the
actual root subgroup, closed immersion, and conjugation equivariance on every
scheme test. The closed immersion is the composite of the additive-group
isomorphism and the pulled-back closed immersion. Equivariance follows by the
injectivity of the pullback point equivalence, with the exact point and character
identities. No affineness, reductivity, or root-datum hypothesis is needed for
this transport theorem beyond its supplied root-parametrization premise.

## Rescaling and Weyl points

`baseScalar_map` proves that the image of `d : R` in the sections of `Z`, viewed
over `R`, equals the image of `algebraMap R A d` using its `A`-structure. It uses
naturality of the sections isomorphism for an affine spectrum.
`baseChangeRoot_scaleHom` then proves the exact group-scheme equality

`baseChangeRoot A (scaleHom d ≫ v) = scaleHom (algebraMap R A d) ≫ baseChangeRoot A v`.

It checks all root-point values and uses injectivity of the point equivalence.

Finally, with `DecidableEq I`, `isWeylPoint_baseChange` preserves a supplied
`IsWeylPoint i (weylPoint u v) f` for any integer exponent automorphism `f`.
The Weyl point of the transported root maps is the three-factor product with
the same coefficients `-1, 1, -1`. The proof transports that product, the torus
map and the exponent automorphism, then applies the supplied conjugation identity
on every test over `A`.

This module does not construct a Weyl-normalized opposite root map, an étale
normalizer lift, or compatible point-group isomorphisms for two reductive groups.
The arbitrary-local-ring Isomorphism Theorem remains open.

# Smooth centralizers of diagonalizable groups

This module constructs a smooth closed representative of the published
`torusCentralizer i` whenever `i : T.toGrp ⟶ G` is a split subtorus of a smooth
affine group scheme over a field `k`. All types and schemes have the arbitrary
universe `u` used by the host statement. No perfectness, characteristic,
maximality, connectedness or reductivity assumption is required. Representation
is on every test scheme over `Spec k`, including non-affine schemes.

## Construction and scope

`smoothCentralizerGroupScheme i hi hG` chooses a group scheme from the proved
existence of a smooth closed representative. Its specification,
`smoothCentralizerGroupScheme_spec`, supplies a homomorphism `j` into `G` such
that `j` is a closed immersion, its source is smooth over `Spec k`, and
`(torusCentralizer i).IsRepresentedBy j`. The last predicate includes monicity
and equality of the range with the published subgroup functor on all tests.
There is no claim that this chosen presentation is unique.

The existence theorem used by the construction is
`torusCentralizer_hasSmoothClosedRepresentative`. Its conclusion is exactly
`(torusCentralizer i).HasSmoothClosedRepresentative`, with assumptions
`IsSplitSubtorus i`, `Smooth G.X.hom` and `IsAffine G.X.left`.

The more general
`diagonalizableCentralizer_hasSmoothClosedRepresentative` allows any additive
commutative character group `M` and a closed homomorphism
`D(M).toGrp ⟶ G`. It does not assume that `M` is finitely generated or
torsion-free.

## Implemented proof

First, `AffineCoordinates.centralizer_hasSquareZeroLifting` works over any
commutative base ring `R` and character group `M`. It assumes that the actual
affine coordinate algebra of `G` is formally smooth over `R`. Its conclusion
is `Corepresented.HasSquareZeroLifting` for the algebra-point family of the
centralizer of `range (AffineCoordinates.coordinateHom i)`. In particular, for
every `R`-algebra `C` and ideal `N` with `N ^ 2 = ⊥`, every centralizer point
over `C ⧸ N` has a centralizer lift over `C`, with the exact reduction equation.

The proof converts the input algebra point to a scheme point on the
corepresented model, then transports it along `AffineCoordinates.groupSchemeIso`.
The published centralizer comparison identifies it with a fixed point of
`AutomorphicAction.conjugation i`. The diagonalizable fixed-point lifting
theorem supplies a lift on `G`. Transporting back along the inverse
isomorphism and using naturality of `affinePointsEquiv` proves membership and
the reduction equation for the required algebra-point family. Fixedness on
both sides retains the quantifier over every refinement of a test scheme.

Over a field, smoothness of `G` gives smoothness, hence formal smoothness and
finite type, of its coordinate algebra `B`. Closedness of `i` supplies an ideal
`I` cutting out its range in the corepresented coordinates. The published
normalizer/centralizer construction cuts out the centralizer by
`J = Corepresented.subgroupCentralizerIdeal e I`, where `e` is the coordinate
corepresentation of `G`. Applying
`Corepresented.formallySmooth_of_hasSquareZeroLifting` to the lifting theorem
proves formal smoothness of `B ⧸ J`. Since the base is a field and `B` is of
finite type, `Corepresented.finitePresentation_quotient` gives finite
presentation. These two properties give `Algebra.Smooth`, and
`Corepresented.smooth_cutGroupScheme` gives smoothness of the actual cut-out
group scheme. The existing closedness and all-test representability theorems
give its inclusion into `G`.

Finally, the split-torus witness identifies `T` with `𝔾_m^I` for a finite type
`I`. The published `Diagonalizable.splitIso` identifies the latter with the
diagonalizable group of the lattice `I → ℤ`. The auxiliary
`SubgroupFunctor.range_precomp_iso` proves that precomposing a homomorphism by
an isomorphism preserves its range on every test scheme. Thus the diagonalizable
case transports to the original, unchanged `torusCentralizer i`.

## Provenance and host boundary

This is an internal construction from the published fixed-point lifting,
affine coordinate, closed centralizer and infinitesimal smoothness APIs. It is
an alternative infinitesimal proof, not a transcription of a further source
theorem. Worker 950 contributed the closed-representative and smoothness
interfaces and their use in this construction.

This unit supplies the centralizer half of
`TorusNormalizerRepresentableStatement`. It does not prove the normalizer half
or complete the host task.

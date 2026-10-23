# Rational similitude group scheme and multiplier

Author: Worker 57.

This module realizes the existing finite-basis similitude functor as an actual
affine group scheme, constructs its multiplier morphism to the existing `Gm`,
and specializes both to the rational involution of a central simple CM algebra.
It identifies finite-adelic scheme points with the already defined adelic
similitudes and checks compatibility with evaluation at a finite place.

## Internal provenance and scope

This is an internal construction from `SimilitudeCoordinates`, `CMData`,
`Adelic`, `GroupScheme.Corepresented`, `CorepresentedPoints` and
`GroupScheme.Multiplicative`. The first module already constructs the explicit
coordinate algebra and its natural classification of scalar-extended
similitudes. The generic adapters turn that proved corepresentation into a
group scheme and recover its points on all test schemes. The present module
supplies the concrete generic and rational specializations and reconstructs
the multiplier from its natural point maps. It asserts no new external
existence theorem. The original arithmetic input and multiplier convention
are those documented in the imported `CMData` and `Similitude` pairs.

The generic base ring `R`, algebra `A` and finite basis index share a universe.
The base is any commutative ring, and `A` is a possibly noncommutative ring
with an `R`-algebra structure. A finite basis and an algebra involution are
inputs. Test schemes range over all schemes over `Spec R` in that universe;
there is no affine or reduced hypothesis on general test schemes. The
rational specialization uses small types for `E`, `K` and `A`, as required
by the same-universe generic construction with `R = ℚ`.

The result constructs the affine group scheme and multiplier. It does not
assert smoothness, reductivity, connectedness, a unitary kernel, a Harris
signature or local splitting, or PEL representability, scheme levels and
coefficient descent. Those remain separate obligations. The finite-adelic
comparison is a multiplicative equivalence of groups; no topology is
introduced on scheme hom-sets here, and no homeomorphism is claimed.

## Generic affine group scheme

The declarations in `AlgebraInvolution.SchemeModel` take a basis `b` and an
involution `σ`. `groupScheme b σ` applies the existing corepresentation adapter
to `σ.similitudeFunctor` and `σ.similitudeCorepresentableBy b`. Both the scheme
and its group operations are constructed from this actual coordinate
presentation; neither is supplied as output data.

`groupScheme_scheme` identifies its underlying scheme with the spectrum of
`σ.similitudeCoordinateRing b`, and `groupScheme_structureMap` identifies its
structure map with `Spec.map` of the scalar inclusion. These are definitional
identities. `groupScheme_isAffine` derives affineness from that spectrum.
The coordinate algebra is the existing presentation recording an invertible
algebra element, an invertible scalar multiplier and the similitude equation;
this module does not replace its relations or its classification proof.

For a commutative `R`-algebra `S`, `affinePointsEquiv b σ S` identifies morphisms
from its relative spectrum with `(σ.baseChange S).similitudes`, preserving the
original group law. Its naturality theorem says that precomposing a scheme
point with the spectrum map of `a : S ⟶ S'` gives exactly `σ.baseChangeMap a`.
Both results specialize the published corepresentation adapter.

For any `T` over `Spec R`, `pointsEquiv b σ T` instead uses the relative
algebra of global sections `((algΓ (CommRingCat.of R)).obj T).unop`.
Its scalar action is supplied by the structural morphism of `T`.
`pointsEquiv_naturality` identifies precomposition by `a : T' ⟶ T` with the
coefficient map supplied by `algΓ.map a`. This is the all-test-scheme
comparison from `CorepresentedPoints`, with no extra affineness condition.

## The actual multiplier morphism

`multiplierPoints b σ T` composes the global point comparison with the
original multiplier homomorphism of the scalar-extended similitude group.
Its values are the actual units of `Γ(T.left, ⊤)`. The theorem
`multiplierPoints_naturality` states that restriction corresponds to
`Units.map` of `a.left.appTop.hom`. After rewriting the naturality of
`pointsEquiv`, this is the defining coefficient-change formula for multipliers.

The private `multiplierAsPoint` converts this unit to a point of the existing
multiplicative group scheme using `Gm.pointsEquiv` in the reverse direction.
Its naturality follows by applying the injective `Gm` point comparison and
using the two restriction formulas. `multiplier` then applies
`GroupScheme.homOfPoints` to these multiplicative maps on every test scheme.
It is therefore an actual group-scheme homomorphism to `Gm`, reconstructed by
group-valued Yoneda.

`multiplier_points` proves that postcomposition with this morphism, followed
by `Gm.pointsEquiv`, equals the original multiplier of the recovered
similitude. The proof uses the reconstruction's point formula and cancels
the `Gm` equivalence with its inverse.

## The CM algebra over the rationals

The declarations in `CentralSimpleUnitaryData` take the existing datum
`D : CentralSimpleUnitaryData E K A n`, with its number-field, CM-extension
and compatible scalar-tower structures. In particular the finite-dimensional
central simple algebra and second-kind involution are actual inputs. The
section additionally uses the compatible `ℚ`-algebra structure on `A`.

`rationalBasis` derives finite dimensionality over `K` from `D.finite`, and
over `ℚ` by transitivity through the number field `K`. It then chooses
`Module.finBasis ℚ A`, indexed by `Fin (Module.finrank ℚ A)`. Thus no rational
basis or rational finite-dimensionality hypothesis is added to the datum.
The chosen presentation is not claimed independent of the basis in this module.

`rationalGroupScheme` applies the generic construction to this rational
basis and `D.toSecondKindInvolution.rationalInvolution`.
`rationalMultiplier` specializes the actual multiplier morphism over
`Spec ℚ`. Consequently its scalar multiplier is rational in the functorial
sense: on a rational test algebra it lies in that algebra's unit group,
rather than an independently chosen center-valued group.

`rationalAffinePointsEquiv` identifies affine points with scalar-extended
similitudes of that rational involution.
`rationalAffinePointsEquiv_naturality` gives the same coefficient-change
formula as the generic result. `finiteAdelicPointsEquiv` specializes to the
existing ring `Global.FiniteAdeles ℚ`, with target exactly the already defined
`FiniteAdelicPoints` group. Finally,
`finiteAdelicPointsEquiv_evaluation` specializes naturality to the algebra
homomorphism `finiteEvaluation v` for an actual finite place of `ℚ`.
The resulting group map is the existing `pointsMap` for that evaluation.
The proof is the rational naturality theorem; it is an algebraic equality,
without a new continuity assertion about scheme hom-sets.

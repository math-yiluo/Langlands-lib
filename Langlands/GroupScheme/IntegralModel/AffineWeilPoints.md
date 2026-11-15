# Integral points of canonical restrictions of integral models

This derived construction identifies the actual sections, integral-point
maps and integral-point subgroups of the canonical restriction constructed
in `Langlands.GroupScheme.IntegralModel.AffineWeilGeneric`. It uses the
existing point functors and the specified generic isomorphism of an
integral model. The comparison square is proved rather than supplied as
an additional hypothesis.

For a commutative ring `R` and any group scheme `X` over `Spec R`,
`AffineWeil.sectionsCoeffEquiv` identifies `rationalPoints X`, whose test
object is the identity of `Spec R`, with
`X.affinePoints (CommAlgCat.of R R)`. It applies the group-valued point
functor to the published identity-test isomorphism `ringTestSelfIso R`.
Both directions preserve the underlying scheme map, as recorded by
`sectionsCoeffEquiv_left` and `sectionsCoeffEquiv_symm_left`.
`sectionsCoeffEquiv_target` gives compatibility with group-scheme
homomorphisms. `sectionsCoeffEquiv_baseChangeSectionHom` identifies
extension of an actual section with coefficient extension followed by
the existing multiplicative base-change point comparison.

Suppose `S` is a finite projective `R`-algebra and `Y` is an affine group
scheme locally of finite type over `S`. Then
`AffineWeil.sectionsEquiv R S Y` is the multiplicative equivalence

`rationalPoints (AffineWeil.groupScheme R S Y) ≃* rationalPoints Y`.

It composes the self-coefficient comparison over `R`, the published
`AffineWeil.basePointsEquiv`, and the inverse self-coefficient comparison
over `S`. Thus it concerns sections of the actual affine restriction.

For the integral-model results, let `A` and `O` be commutative domains
with fraction fields `F` and `K`. Assume that `O` is finite projective
over `A`, that `K` is an `F`-algebra, and that the specified maps from
`A` to `K` through `O` and through `F` agree. All types lie in an
arbitrary common universe `u`. Let `G` be an affine group scheme locally
of finite type over `K`, and let `M : IntegralModel O K G` have smooth
integral group. These are the assumptions of the canonical restricted
model `AffineWeilGeneric.model A F O K M`. Localness, unramifiedness and
separability are not additional assumptions of this comparison.

All the following names are in `IntegralModel.AffineWeilGeneric`.
`genericSectionsEquiv` identifies rational points of the actual generic
restriction `genericGroup A F O K G` with rational points of `G`.
Finiteness of `K` over `F` is derived by the imported `genericFinite`.
`modelSectionsEquiv` identifies integral sections of the canonical
restricted model with integral sections of `M`.

The coefficient calculations keep an abstract bundled `F`-algebra `R`
until the final specialization to its self test. `integralTestMap`
is the coefficient map from `A` into that algebra.
`sectionsCoeffEquiv_baseChangeSelf` expresses actual extension from `A`
to `F` with these precise bundled structures. For every
`K`-algebra homomorphism `b : K ⊗[F] R →ₐ[K] K`,
`coefficientEquiv_integral` proves that the composite

`O ⊗[A] A → O ⊗[A] R → K ⊗[F] R → K`

equals tensor-unit evaluation `O ⊗[A] A → O` followed by `O → K`.
The proof is tensor induction: on pure tensors it uses the published
formula for `coefficientEquiv`, scalar compatibility and the fact that
`b` fixes `K`. Additivity handles sums.

`integralTensorPointsEquiv` is naturality of the restriction point
equivalence under the integral coefficient map.
`coefficientPoints_integral` applies the preceding coefficient identity
to the existing affine-point functor.
`genericTensorPointsEquiv_coefficient` gives compatibility of the
generic tensor-point comparison with `b`, using base-change naturality
and the original generic identification.

`model_integralPointMap` proves, for every integral section `x` of the
canonical restricted model, the equality

`genericSectionsEquiv (model.integralPointMap x) =
 M.integralPointMap (modelSectionsEquiv x)`.

The proof passes to self-coefficient points, evaluates the canonical
generic isomorphism using its published point formula, cancels the
restriction and base-change equivalences, and applies the three
coefficient identities with tensor-unit evaluation. Extension of the
original section followed by `M.genericIso` is precisely the original
integral-point map. No injectivity of either integral-point map is
assumed.

`model_mem_integralPoints` gives membership equivalence under
`genericSectionsEquiv`. In the forward direction it maps a witnessing
integral section with `modelSectionsEquiv`. In the reverse direction it
uses the inverse section equivalence and injectivity of the generic
point equivalence. `model_integralPoints_comap` and
`model_integralPoints_map` state the resulting equalities of actual
subgroups, using the monoid homomorphism of `genericSectionsEquiv`.

The provenance is internal: these constructions compose the published
identity-test, affine restriction, coefficient pushout and generic
comparison APIs. The additional proofs verify their action on actual
sections and the range of the integral-point homomorphism. They support
identification of canonical restricted models with root filtrations;
they do not establish that identification, an isomorphism to an
arbitrary supplied model, or the full root-depth kernel theorem.

# Constant-term transport under actual group-scheme isomorphisms

This internal construction combines the actual continuous function
pullback with the actual subgroup-quotient homeomorphism. For an isomorphism
`e : G ≅ H` of affine group schemes over an arbitrary-universe number field
and a subgroup functor `V` of `H`, its source subgroup is the existing
`V.comap e.hom`. The integrand of the pullback of `f` at `g` is the integrand
of `f` at the actual image of `g`, composed with `rationalQuotientIso F e V`.
The proof descends to representatives and uses preservation of multiplication.

The measure results assume that both ambient group schemes are locally of
finite type, that the actual adelic subgroup of `V` is closed, and that
`V(F) \ V(A_F)` is compact. Source closedness is derived from target closedness.
With the existing intrinsic normalized rational quotient Haar measures,
the change of variables proves a separate equivalence of Bochner integrability
and equality of the totalized constant terms. No measure identity is assumed
and no replacement target measure is defined.

Surjectivity of the actual ambient point isomorphism upgrades these pointwise
identities to equivalence of the original global convergence conditions and
of the conditions requiring convergence and vanishing at every argument.
The function spaces and the constant-term definitions remain the published
ones, with positive right translation.

`vanishingConstantTermPullbackEquiv` restricts the ambient pullback linear
equivalence to the existing convergent vanishing subspaces for these two
subgroups. The proved vanishing equivalence identifies the target submodule
with the inverse image of the source submodule, and the ordinary submodule
restriction of the ambient equivalence supplies the inverse. The evaluation
lemmas identify the forward and inverse maps with pullback along `e.hom`
and `e.inv`. Its right-action theorem inherits the positive ambient
intertwining identity.

The provenance is internal: the proof uses the existing function pullback,
actual quotient transport, and intrinsic probability preservation APIs.
There is no external source assertion, no identification of radical functors
under conjugation, no classification of rational parabolics, and no iterated
integration or general reductive finite-volume assertion.

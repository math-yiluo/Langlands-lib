# Centralizing charts from residue-maximal integral tori

This internal construction assembles the integral conjugacy and descended-torus
arguments for an arbitrary same-universe field extension `K/F`. Let `G/F` be
a group scheme, `i:T → G` and `j:T' → G` maps of commutative group schemes,
and `D` the supplied apartment data for `i_K`. The underlying scheme map
of `i_K` is monomorphic and `G_K` is affine. The conclusion concerns this
same original reduced building. No local-field or characteristic condition
is imposed.

The input model `M` is a smooth integral model of the connected reductive
group `G_K` over a Henselian local domain `R` with fraction field `K`. There
is a surjective algebra map `R → k` to a field and the actual `k`-fibre of
`M.group` is connected. A supplied split commutative group `A/K` with
map `a:A → G_K` factors through both `i_K` and `j_K` by specified maps
`f,f'` and exact commuting equations. Only `i_K` is assumed maximal split.

For any subset `Y` of the supplied reduced building, assume `M.integralPoints`
fixes `Y` pointwise. A supplied point `q ∈ G_K(K)` gives a translated original
chart covering `Y`. Two actual split integral tori `T₀,T₁/R` have maps
`i₀:T₀ → M.group` and `i₁:T₁ → M.group`. The reference map `i₀` is a
closed subgroup. Supply actual generic source isomorphisms
`e₀:T₀,K ≅ T_K` and `e₁:T₁,K ≅ T'_K`, with exact squares

- `M.genericHom i₀ = groupHom e₀.hom ≫ (i_K ≫ Int(q))`;
- `M.genericHom i₁ = groupHom e₁.hom ≫ j_K`.

The actual `k`-fibre of `i₁` is maximal split. All torus objects, maps,
isomorphisms and squares are explicit arguments. Target generic maximality
is derived.

`D.centralizingConjOfResidueMaximalIntegralTorus` returns an actual rational
point `g` with a certificate that:

- `g ∈ centralizerPoints a`;
- `g⁻¹ * rationalConjugate F K G σ g` normalizes `i_K` for every
  `σ : K ≃ₐ[F] K`;
- the original apartment translated by `g` covers `Y`.

The implementation first transports maximality of `i_K` through `Int(q)`
and the reference generic source isomorphism. It constructs an actual
integral conjugator `B` from the target residue maximality and the reference
generic maximality using
`IntegralModel.henselianSplitTorusConjugatorOfResidueGeneric`. The exact
generic conjugacy transfers maximality to `M.genericHom i₁`,
then the target generic source isomorphism transfers it to `j_K`.

The inverse of the same actual generic conjugator changes the chart point
to `g₀ = (B.genericPoint M)⁻¹ * q`. Its source isomorphism is the composite
of the inverse reference generic isomorphism, inverse generic integral
conjugacy isomorphism, and target generic isomorphism. The proved
`SplitTorusConjugator.inverse_translated_generic_comm` supplies its exact
conjugation square after substituting the supplied target generic square.
`subset_range_integralConjugacyApartmentMap` proves this chart still covers
`Y`, because the inverse integral point fixes every point in `Y`.

Finally `centralizingConjCoveringOfDescendedTorus` replaces `g₀` by its
selected centralizing representative without changing the chart's covered
points. It supplies centralizer membership and all normalizer-valued
coefficient differences; its chart-membership equivalence transfers the
just-proved coverage point by point.

The provenance is derived assembly of `IntegralModel.ResidueMaximalSplitTorus`,
`IntegralConjugacyApartmentContainment`, `CentralizingDescendedApartment`
and the actual model `genericHom` interface. Its explicit integral-torus
arguments can be supplied by projecting compatible integral-torus data; it
does not import the integral root-filtration development. The construction
does not assume a
generic conjugation square from the original to the target torus, target
generic maximality, or target chart coverage. It does retain existence of the
model, initial integral covering chart, residue-maximal integral split target
torus, and its factorization of `a`. Constructing those data from a pair of
coefficient-fixed unit-fixed points is not done here;
`UnramifiedFixedPairSpecialApartmentStatement`, which needs them, is proved
separately in `UnramifiedFixedPairSpecialApartmentProof`.

# Supported coefficient complexes on induced rational spectra

This internal construction applies the actual compact-support function functor
on induced rational spectra degreewise to complexes of smooth coefficients.
It also prolongs proper transport pullback to natural chain maps and to maps
on the homology of those specific complexes. The input complex is supplied;
it is not claimed to be a resolution computing geometric cohomology.

## Inputs

The base field, affinoid algebra, topological operator group and rational
spectral action are those of `InducedRationalCompactSupport`. The coefficient
ring is an arbitrary commutative ring. Field, group, coefficient-ring,
coefficient-module and indexing universes are independent. If coefficients
have carrier universe `w`, supported functions have carrier universe
`max u v w`. Coefficients have no topology, and there is no finite-dimensionality,
nonemptiness, separation or finiteness-of-cosets assumption.

## Complexes and homology

`coefficientFunctor_additive` proves additivity by evaluating both sides at a
supported function and a point. Thus Mathlib's `mapHomologicalComplex` applies:
its differential is the original coefficient differential applied pointwise.
It proves all complex-shape and differential-square obligations from
functoriality and preservation of zero. `supportedComplexFunctor` allows any
`ComplexShape` on any indexing type, and is additive on chain maps.
`supportedCochainFunctor` specializes to nonnegative cochains.

`supportedHomologyFunctor` is the homology of this constructed complex in the
published abelian category of smooth representations. It therefore retains a
smooth full-group action. No exactness of the supported coefficient functor,
comparison with the homology of the input, or sheaf cohomology comparison is
used or claimed.

## Proper transport

`compactSupportPullbackNatTrans` packages the already proved coefficient
naturality of actual precomposition by a proper induced transport map.
`compactComplexPullbackNatTrans` is its Mathlib prolongation. Its component
in each degree evaluates to `s(f.inducedMap z)`, and its chain-map equation
comes from coefficient naturality. The identity and contravariant composition
laws follow from the corresponding function-level identities and Mathlib's
identity/composition laws for prolongation. Whiskering with the homology
functor gives `compactHomologyPullbackNatTrans` and its identity/composition
laws. Properness is still an explicit input for every nonidentity arrow.

## Provenance and boundaries

This is derived infrastructure from the actual induced rational spectrum,
the proved full compact-support smooth function functor, the published
abelian smooth representation category, and the pinned Mathlib
`Algebra.Homology.Additive` and
`Algebra.Homology.ShortComplex.HomologicalComplex` constructions. It makes no
new original-literature claim. Analytic or etale sheaves, a geometric
resolution, derived compact-support comparison, arithmetic coefficient
systems, towers and Harris specialization remain separate constructions.

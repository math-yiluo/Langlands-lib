# Invariant polynomials and flat surjective restriction

This internal construction names the all-test-scheme polynomial invariance condition
used in `ReductiveGeometricReductivityStatement`. It proves an elementary descent
lemma for that condition. It does not construct a reductive cover or prove Haboush's
theorem.

For any commutative coefficient ring `R`, an actual `MatrixRepresentation G n`, and
`F : MvPolynomial n R`, `MatrixRepresentation.IsInvariantPolynomial` says that
evaluation of `F` is unchanged by the action of every `g : G(T)` on every vector
with entries in the global sections of every scheme `T` over `Spec R`. There is
no restriction to affine, reduced, or field-valued test schemes.

`eval₂_scalarMap_naturality` proves that evaluation commutes with pullback along a
relative test map, using naturality of the structural coefficient map and
commutation of multivariate polynomial evaluation with a ring homomorphism.
`IsInvariantPolynomial.restrict` restricts invariance along any actual group
homomorphism.

`isInvariantPolynomial_restrict_iff` reflects invariance along a homomorphism
`q : H ⟶ G` whose underlying scheme map is flat and surjective. Given an arbitrary
test point `g : T ⟶ G`, form the scheme pullback `U = T ×_G H`. Its projection
`a : U ⟶ T` is flat and surjective and is therefore an epimorphism. The tautological
point of `H` over `U` gives the desired invariant evaluation identity after pullback
along `a`. Naturality of the representation matrices, matrix multiplication and
polynomial evaluation identifies it with the pullback of the original identity.
Pullback of global sections along a scheme epimorphism is injective, so that
identity already holds on `T`. The argument requires no surjectivity on `T`-points.

The provenance is derived: these are direct consequences of the existing Library's
actual coefficient representations, their naturality, and its global-function
injectivity lemma, together with Mathlib's stability of flat surjections under
pullback and their epimorphism property. The predicate is precisely the invariance
clause in the published geometric-reductivity target, with no homogeneity or
nonvanishing condition included. Those conditions concern the same polynomial and
are unchanged by restriction.

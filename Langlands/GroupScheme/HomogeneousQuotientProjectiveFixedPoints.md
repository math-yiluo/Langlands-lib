# Fixed-point dimension bounds for actual proper homogeneous quotients

This internal assembly applies the explicit
`ProjectiveTorusFixedPointDimensionStatement` to the actual projective embedding
of a supplied homogeneous quotient. The projective fixed-point theorem remains
a premise; this module does not prove it.

The field `k : Type u` is algebraically closed, in arbitrary characteristic.
The ambient group `G` is smooth, affine and connected, and the supplied subgroup
`b : B ⟶ G` is closed. The supplied projection `q : G.X ⟶ Q` is smooth,
surjective and quasi-compact, and `Q` is proper over `Spec k`. Its fibers obey
the exact right-coset law on every relative scheme test:
`q(g) = q(h)` if and only if `g⁻¹ * h` belongs to the range of `b`.
No solvability, reductivity or maximality is required for the first construction.

`projectiveFixedPointEmbedding` also takes a split torus `T`, an arbitrary
homomorphism `i : T.toGrp ⟶ G`, and a natural number `d` below the actual
topological Krull dimension of `Q`. Given the projective fixed-point statement,
it constructs an embedding of `Fin (d + 1)` into the rational sections of this
same quotient fixed on all relative tests by its canonical action restricted
along `i`. The map `i` need not be monic.

The construction derives smoothness, reducedness and irreducibility of `Q`
from the published smooth-quotient comparison. Smoothness gives local finite
type, properness gives quasi-compactness, and irreducibility gives nonemptiness,
so the full finite-type projective fixed-point statement applies. The actual
matrix representation and projective closed embedding are obtained from
`projectiveEmbeddingData`; subgroup smoothness is derived inside that
constructor. The representation and action are restricted together along `i`,
and `restrict_equivariant` gives matrix equivariance of the same embedding.
The fixed-point family supplied by the explicit statement is then regarded as
an injective family in the subtype of all-test fixed points.

`dimension_le_one_of_projectiveFixedPointDimension` further assumes that `G` is
connected reductive, `i` is a split maximal torus, and any two actual roots of
`i` are integrally dependent. The torus factors through this same subgroup `B`,
maximal tori are conjugate inside `B`, and the rational points of the whole-torus
centralizer belong to its range. The existing rank-one fixed-point sign
embedding puts the fixed rational points in `Bool`. If dimension were at least
two, the preceding construction with `d = 2` would embed `Fin 3` into those
fixed points, which is impossible. Hence the actual topological Krull dimension
is at most one.

Provenance is the composition of the named internal quotient, projective
embedding and fixed-point counting constructions. The generic geometric
fixed-point theorem is used only through its named proposition premise.
No representation, projective embedding, reducedness, nonemptiness, quotient
dimension bound or fixed-point family is separately supplied by the caller.
Quotient existence and properness, the generic fixed-point proof, internal torus
conjugacy and rational-centralizer containment are still application obligations.
No unconditional positive-root uniqueness theorem is asserted.

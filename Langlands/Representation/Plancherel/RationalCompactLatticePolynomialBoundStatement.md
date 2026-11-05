# Polynomial coefficient bounds on compact actual lattice charts

`Langlands.Plancherel.RationalCompactLatticePolynomialBoundStatement` is a
derived analytic intermediate for coefficientwise moderate growth. It uses
actual rational points of any connected reductive group over a nonarchimedean
local field, the canonical point topology, the residue-normalized
`MatrixRepresentation.rationalMatrixNorm`, and a smooth complex representation
with independent field and carrier universes. No admissibility, finite length,
closedness of the matrix representation, splitness, or characteristic
restriction is needed for this intermediate.

Let `τ` be any family indexed by natural coordinates on a finite type `I`.
Assume every smooth coefficient along `τ` has a product-exponential bound with
positive coordinate radii. The radii and positive constant may depend on the
vector and functional. Assume also a geometric coordinate comparison: there
are real numbers `q > 1` and `A > 0` such that

`q ^ (∑ i, m i) ≤ A * rationalMatrixNorm F ρ (τ m)`

for every coordinate tuple `m`. Then each coefficient on
`k₁ * τ m * t * k₂`, with `k₁` and `k₂` ranging over two supplied compact sets
and `t` over a supplied finite set, is bounded by a positive constant times an
integer power of the matrix norm of that same translated point. The exponent
and constant may depend on the coefficient and the three sets, but work
uniformly for every coordinate tuple and translating point.

This statement permits an empty coordinate type and empty translating sets.
It does not require `τ` to be a homomorphism. Its provenance is internal:
finite compact orbits extend the product bound to the translates; a single
integer power of `q` dominates all the finitely many radii; and bounded matrix
norms on compact sets compare the norm of `τ m` with the norm of its translate.

The coordinate comparison is an explicit remaining geometric premise. This
statement supplies neither that comparison nor a Cartan cover, central-factor
control, or the existence of compatible standard compact subgroups. Its
conclusion is confined to the supplied charts and does not assert the full
`RationalCoefficientModerateGrowthStatement`.

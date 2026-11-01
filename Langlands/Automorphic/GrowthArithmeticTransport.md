# Arithmetic transport of adelic polynomial-growth functions

Author: Worker 2.

For actual number fields `K`, `L` in independent universes, any natural
matrix rank, and an actual field isomorphism `e : K ≃+* L`, this internal
construction restricts the existing arithmetic pullback to three existing
subspaces of the continuous complex-valued rational-invariant adelic
functions. The complex values are unchanged by pullback.

`arithmeticComap_hasPolynomialGrowth` proves the slice-dependent growth
condition from `Automorphic.Growth`. At a finite argument `b` of the source,
the infinite slice is the old slice at `finiteEquiv n e b` precomposed by
the actual infinite arithmetic matrix map. The archimedean growth estimate
therefore gives its bound. More explicitly, an old bound with nonnegative
constant `C` and natural exponent `d` on that image slice becomes a bound
with constant `C * ArchimedeanGLTransport.growthBound n e ^ d` and the same
exponent. Constants and exponents may depend on `b`; no bound uniform in
the finite argument is imposed. Applying the result to `e.symm` proves
reflection. The membership equivalence expresses this result for the
existing polynomial-growth subrepresentation.

The two further membership equivalences combine growth with the already
proved arithmetic preservation and reflection of the existing smoothness
conditions. `smoothPolynomialGrowthSubrepresentation` requires real
smoothness on each infinite slice and local constancy on each finite
slice. `finiteSmoothPolynomialGrowthSubrepresentation` instead requires
real smoothness and a common open finite-adelic stabilizer. The names
refer to those exact existing intersections.

`polynomialGrowthEquiv`, `smoothPolynomialGrowthEquiv`, and
`finiteSmoothPolynomialGrowthEquiv` are actual continuous complex-linear
equivalences on these three subspaces. Their topologies are inherited
from the ambient continuous functions with the compact-open topology.
Each construction restricts `arithmeticEquiv` using its proved subspace
image equality. Thus its inverse is pullback along `e.symm`. Forward and
inverse evaluation formulas, identity, contravariant composition, and
equality of the inverse equivalence with the inverse-field construction
are provided for each.

All three equivalences intertwine the full adelic right actions through
`AdelicGLTransport.adelicEquiv n e`, with convention `R(g)f(x) = f(x * g)`.
The growth equivalence commutes with the published faithful inclusion
into ambient continuous functions. The smooth growth equivalence also
commutes with the existing inclusion from the common-stabilizer growth
space.

Provenance is internal. The proof composes the actual slice identity from
`SmoothArithmeticTransport`, the concrete matrix/inverse height estimate
from `ArchimedeanGrowthTransport`, and the existing smoothness equivalences.
Subspace image equality follows from the membership equivalences and
surjectivity of the existing ambient equivalence. No new literature
identification is claimed. In particular, this construction retains the
specified matrix height; it supplies no comparison with another source
norm or source slow increase. It asserts no continuity for a derivative
topology, no preservation of enveloping-center finiteness or cuspidality,
and no automorphic occurrence or existence.

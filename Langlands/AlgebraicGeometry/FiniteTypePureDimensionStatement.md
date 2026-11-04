# Pure dimension under arbitrary field extension

This internal algebraic prerequisite is motivated by the last fibre
property in Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), printed pp. 5–6, Theorem 3.4(2). That property includes
pure dimension d of every residue-field fibre. The proposition here is a
separate scalar-extension comparison needed for that development; it is
not the filtered-descent theorem of Conrad.

The source is registered as `conrad-2011-weil-grothendieck-adelic-points`,
SHA-256 `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The statement is derived: the arbitrary-extension algebra comparison is
not attributed as a separate numbered statement to Conrad. Its proof can
be obtained from Noether normalization and minimal-prime quotients.

`FiniteTypeFieldExtensionPureRingDimensionInvariance` quantifies a field k,
a field extension K, and a finite-type commutative k-algebra A, in three
independent universes. For each natural number d it states that A has
`HasPureRingDimension` d if and only if the actual tensor algebra
A tensor_k K has that property. The predicate fixes the Krull dimension
of every minimal-prime quotient to d, as an equality in WithBot ℕ∞; the
published affine comparison identifies it with dimension d on every
irreducible component of the spectrum.

There is no domain, reducedness, separability, algebraicity or finiteness
assumption on K/k. A can have zero divisors or be the zero ring. In the
zero-ring case the componentwise condition is vacuous on both sides.
The finite-type assumption on A is retained for arbitrary K/k. This differs
from `AlgebraicFieldExtensionPureRingDimensionInvariance`, which permits
arbitrary A but assumes K/k algebraic, and from the statement comparing
only total Krull dimension.

The intended proof first treats finite-type domains using a finite
injective Noether normalization and torsion-free integral scalar
extension. It then compares each minimal-prime quotient after extension
with the quotient by its contracted prime, using the actual
tensor-quotient equivalence. Flat going down contracts minimal primes;
injectivity of A into its scalar extension lifts them for the reverse
implication. This statement supplies no scheme base-change comparison,
constructibility or filtered fibre descent, and proves no part of those
remaining obligations by itself.

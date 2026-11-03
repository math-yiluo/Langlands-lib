# Positive characters across finite index

This internal algebraic construction extends a character from a finite-index
subgroup `H` of an arbitrary commutative group `A` to the units of the
nonnegative real numbers. It has no topology or finite-generation requirement
on `A`. The group universe is arbitrary.

`finiteIndexExtension H χ` sends `a` to the positive `H.index`-th root of
`χ(a ^ H.index)`. Normality of `H` makes the indicated power an element of `H`,
and commutativity makes this power map a homomorphism. The real power map on
nonnegative reals is multiplicative, so the formula defines a character.
Finite index makes the exponent nonzero. Mathlib's positive-root cancellation
identity proves that the restriction is `χ`. Any other extension agrees after
raising values to `H.index`, and the same cancellation identity proves
uniqueness.

The module also proves that a positive character with open kernel is trivial
on a compact group with separately continuous multiplication, and hence on
any compact subgroup of a topological group. The quotient by its open kernel
is compact and discrete, hence finite. Every value therefore has finite order;
injectivity of positive natural powers makes it one.

The content is derived from Mathlib's subgroup-index, quotient-topology and
nonnegative-real-power results. It is an algebraic prerequisite for central
unitarization. No rational-point structure, finite-index central image,
compact central kernel, representation-theoretic theorem, or Levi
self-association is asserted here.

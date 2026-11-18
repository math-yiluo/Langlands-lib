# Uniform-exponent assembly from Artinian bases and exhaustion

This internal reduction proves that the unchanged quasi-finite commutative
uniform-exponent target follows from two explicitly retained inputs:
`ArtinianUniformExponent.Statement` and
`QuasiFiniteArtinianExhaustionStatement`. It proves the Prop-valued
`UniformExponentReduction.Statement`; it does not supply either input.

Over a noetherian affine base, local finite presentation supplies the explicit
local-finite-type hypothesis of the exhaustion input. The proof takes the actual scheme-theoretic
equalizer of multiplication by `i!` and the constant unit map for each natural
number `i`. These are subscheme immersions, without a separatedness assumption.
The factorial divisibility relation makes this a directed increasing sequence.
The inclusion of the `i`-th equalizer is a point of the original group over
its own source scheme; its `i!`-th power is one, and hence its `k!`-th power is
one whenever `i ≤ k`. The equalizer's universal property gives the inclusion
into the `k`-th subscheme.

After a local Artinian base change, the Artinian input gives a positive exponent
`m` on all test schemes. Since `m` divides `m!`, the universal point of that
base-changed group is killed by `m!`. The multiplicative pullback point
equivalence translates this into a factorization of the projection to the
original group through the `m`-th equalizer. Its pulled-back inclusion is
therefore a split epimorphism as well as a monomorphism, hence an isomorphism.
The exhaustion input now makes one of the original equalizer inclusions an
isomorphism. Its defining equation says that multiplication by `i!` is the
unit map. Positivity of `i!` and Yoneda evaluation give the required exponent
on all points.

The final theorem uses the already implemented finite-presentation
noetherian approximation and finite affine-cover reductions to reach the
original target over an arbitrary quasi-compact base.

This is a categorical elaboration of SGA 3, Exposé IX, proof of Lemma 6.1
through Lemma 6.2, printed pp.52–54 (retained PDF pp.22–24), registered as
`sga3-expose-ix-gille-polo-2009`, SHA256
`7c1e3d5b9d01ad01d0dd7b8b62045d012052e7890fb37adc3e7934ebb5fd6fc3`.
Using factorials replaces the source's family indexed by positive integers
ordered by divisibility with an ordinary increasing sequence.

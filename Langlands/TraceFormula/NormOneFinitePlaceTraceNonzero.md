# Nonvanishing of an isolated trace from two orbital factors

`NormOneFinitePlaceTraceNonzeroStatement` concerns a rational orbit in the
norm-one adelic group. It uses a central split torus whose character restriction
is injective with finite-index image. The adelic Haar measure on the norm-one
group is right invariant, the automorphism fixes the central morphism, and the
selected twisted centralizer is commutative.

The test is the positive-torus average of a distinguished finite-place factor
times an exterior factor invariant under that local group. The local orbital
value for the supplied compatible measures is nonzero. The exterior value is
nonzero for each nonzero regular right-invariant measure on the exterior
centralizer quotient. The trace identity and the implication from nonzero
global orbital value to finite rational covolume hold for every compatible
geometric measure package.

The proof uses `normOneFinitePlaceGeometricTerm` to extend the specified local
normalization. Its factorization gives a nonzero global orbital value from the
two factors. The finiteness implication and
`TwistedGeometricMeasures.covolume_ne_zero` give a nonzero covolume scalar, so
the trace, which is the covolume times the orbital value, is nonzero.

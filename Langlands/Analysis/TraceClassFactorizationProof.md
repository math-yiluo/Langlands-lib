# Proof of trace-class factorization

`Langlands.Analysis.OperatorIdeals.traceClassFactorization` proves
the full `TraceClassFactorizationStatement` for arbitrary complete
complex inner-product spaces.

Let L be the positive left modulus of A, and B its positive square
root. Continuous functional calculus gives B squared equals L and
self-adjointness of B. The adjoint identity for the squared norm
then identifies `‖B x‖ ^ 2` with the real part of `inner ℂ x (L x)`.
Applying this pointwise identity to the actual trace-class witness
basis supplies the existential Hilbert–Schmidt witness for B.

The published `leftModulusFactorization` theorem provides a
contractive bounded endomorphism U with A = L U. Set C = B U.
The published Hilbert–Schmidt precomposition law proves that C
is Hilbert–Schmidt. Evaluation at each vector and B squared equals L
give A = B C, with composition in the stated order.

The diagonal helper rederives the same continuous-functional-calculus
identity used privately in `TraceNormBasisProof`; it imports no
unpublished helper. The statement Markdown records the original
left-modulus convention and the internal provenance of this intermediate
result. No trace identity, spectral decomposition, separability, or
converse trace-class product theorem is assumed.

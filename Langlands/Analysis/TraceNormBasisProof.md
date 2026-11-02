# Proof of trace-class basis characterization and trace-norm independence

`Langlands.Analysis.OperatorIdeals.traceNormBasisIndependence` proves
`TraceNormBasisIndependenceStatement` with its three independent
universe parameters. It retains complete complex inner-product spaces
and arbitrary Hilbert-basis index types, including nonseparable spaces.

The statement Markdown records the original Getz–Hahn definition,
equation, independence assertion and exercise, the registered source and
errata fingerprints, the positive left-modulus convention and the
derived arbitrary-index scope. This proof uses continuous functional
calculus and the already published Hilbert–Schmidt basis-independence
theorem; no proof of the target is supplied as a hypothesis.

For `L = leftModulus A = sqrt(A A*)` and `B = sqrt L`, functional
calculus gives positivity of L and B, the equality `B² = L` and
self-adjointness of B. The continuous-linear-map adjoint identity yields
`‖B x‖² = Re⟪x, B* B x⟫ = Re⟪x, L x⟫`.
The first private lemma states this equality in the direction from
the real modulus diagonal to the squared norm.

Applying `hilbertSchmidtBasisIndependence E E ι κ B b c` and rewriting
with that equality gives both summability equivalence of the two real
diagonal families and equality of their sums whenever the first is
summable. Unfolding the existing `traceNormIn` definition identifies the
sums with the specified-basis trace norms. The proof reuses the published
Parseval and nonnegative-double-sum argument through that theorem; it
does not repeat it or require any separability hypothesis.

For the trace-class characterization, a witness for `IsTraceClass A`
is a Hilbert basis d indexed by a subset of E and a summable modulus
diagonal. The preceding equivalence transfers that summability to the
given basis b. Conversely, `exists_hilbertBasis` supplies such a
subset-indexed basis d, and transferring summability from b to d
provides exactly the existential witness required by `IsTraceClass`.

The final theorem packages this characterization and the two-basis
conclusions into the exact proposition. All helper lemmas are private.
There is no chosen canonical norm, complex trace diagonal result or
automorphic trace-class construction in this module.

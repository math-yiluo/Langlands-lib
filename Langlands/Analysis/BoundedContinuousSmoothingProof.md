# Proof of the bounded-continuous smoothing criteria

Worker 116 implements `boundedContinuousSmoothingCriteria`, the exact
conjunction `BoundedContinuousSmoothingCriteriaStatement`, with component
theorems `hilbertSchmidtBoundedContinuousLift` and
`traceClassFiniteFactorizationSmoothing` at independent universes u, v, w.

For a bounded-continuous lift S of j∘A, the first theorem takes B=j∘A
and evaluation functionals k(x)=evalₓ∘S. Mathlib's `coeFn_toLp` supplies
the vectorwise almost-everywhere representation of B(z). The sup-norm
bound for evaluation followed by S's operator-norm bound gives
‖k(x)‖≤‖S‖ for every x. The uniform finite-measure evaluation criterion
therefore makes B Hilbert–Schmidt. On its witnessing Hilbert basis, j's
norm preservation identifies every squared norm for B with that for A,
so the same basis and summability witness make A Hilbert–Schmidt.

The second theorem applies that lift criterion separately to every f
using the supplied lift of R(f). It then writes an arbitrary f as its
supplied finite sum of products. Multiplicativity identifies the operator
of each product aᵢbᵢ with R(aᵢ)∘R(bᵢ). The published Hilbert–Schmidt
product theorem makes this composition trace class. Finite-set induction,
using the published trace-class zero and addition laws, makes the finite
sum trace class. Additivity of R and the factorization identity identify
the sum with R(f). The conjunction theorem pairs these two results.

The mathematical provenance is the internal adapter explained in the
target Markdown, motivated by Getz–Hahn (2024), Lemma 9.3.3,
printed pp.247–248, and Theorem 4.2.9, printed p.110. This proof uses the
explicit factorization hypothesis; it proves no Dixmier–Malliavin theorem
or adelic smoothing estimate. Its route uses the evaluation criterion
rather than the source's two-variable kernel construction.

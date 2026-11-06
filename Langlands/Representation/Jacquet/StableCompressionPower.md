# Fixed-exponent stability of compact compression

Worker 1751. This internal algebraic interface packages the published compact
compression of a smooth complex representation. It does not prove that a stable
power exists for an arbitrary smooth representation or that its exponent can be
chosen independently of the representation.

The source comparison is Renard 2026, Appendix C.II, Definition and Lemma (i),
(iv), printed pp.276–278 / PDF pp.282–284, and VI.9.1 Proposition, printed p.197 /
PDF p.203. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The new predicates are derived internal packaging, not additional assertions
attributed to Renard. The implemented argument reuses the independently
published arbitrary-dimensional C.II proof in
`Langlands.LinearAlgebra.StableEndomorphismProofs`.

For a topological group G, a smooth complex representation rho on V, a compact
open subgroup K and g in G, let C be `Jacquet.compressedAction rho h_rho K h_K g`.
`CompactCompressionStablePower ... b` means `Stable (C ^ b)`, namely equality
of the kernel and range of C^b with those of (C^b)^2. Its definition does not
require b to be positive. `CompactCompressionStationaryFrom ... b` means that
at every exponent s at least b the range of C^s is the published `stableImage`,
the kernel is `powerKernelSup`, and those two limit submodules are complementary.
These are exactly the pointwise conclusions used by the uniform VI.9.1 target.

For b > 0, the predicates are equivalent at that same exponent. From a stable
power, rewrite (C^b)^2 as C^(2b). Monotonicity of the kernel chain and
antitonicity of the range chain, together with b+1 <= 2b, give equality between
exponents b and b+1. The published adjacent-equality lemmas propagate each
chain equality to every later exponent. The limit supremum and infimum equal
the values at b because earlier terms lie on the appropriate side of those
values. The published stable-kernel/range criterion gives complementarity.
The converse compares the two stationary-chain equalities at b and 2b; it does
not require positivity.

Increasing the threshold preserves stationarity and splitting. Consequently,
existence of stationary chains with splitting is equivalent to the published
`EventuallyStable C`, which requires a positive stable power. For a stationary
threshold that may be zero, replace it by max b 1 before applying the converse.
The individual stable-power criterion is also recorded directly as equivalence
with complementarity of ker C^b and range C^b.

All proofs concern arbitrary-dimensional vector spaces. The group and carrier
universes are independent. There are no parabolic, contraction, centrality,
admissibility or representation-finiteness hypotheses. Such hypotheses are
needed to establish stable-power existence in the VI.9.1 application; this
module only establishes the subsequent algebraic passage without changing its
exponent.

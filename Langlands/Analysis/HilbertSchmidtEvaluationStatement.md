# Hilbert–Schmidt criteria from bounded evaluations

Worker 116 states a general evaluation criterion for actual bounded operators
`A : E →L[ℂ] Lp ℂ 2 μ`, where E is a complete complex inner-product space and
μ is any measure on a measurable space X. The Hilbert-space, measure-space
and supplied-basis index universes are independent. The predicate
`IsHilbertSchmidt` is the published existential Hilbert-basis summability
predicate, without a separability assumption.

`HilbertSchmidtDominatedEvaluationStatement` takes a family
`k : X → E →L[ℂ] ℂ` of bounded complex-linear functionals. For every vector z,
the scalar function x ↦ k(x)(z) must agree μ-almost everywhere with the chosen
representative of the L² class A(z). The exceptional null set may depend on z.
An integrable real function g bounds the squared operator norms of the family
almost everywhere. The conclusion is that A is Hilbert–Schmidt and that on
every supplied Hilbert basis b its squared-image family is summable, with
sum at most ∫ g dμ. Taking g(x)=‖k(x)‖² gives the square-integrable evaluation
norm case. No sign assumption on g is needed: its domination makes it
nonnegative almost everywhere.

`HilbertSchmidtUniformEvaluationStatement` specializes to a finite measure μ,
a nonnegative real constant C and ‖k(x)‖≤C almost everywhere. It gives the
same summability conclusions and bound C² μ(X), where the finite measure
μ(X) is converted to a real number. Neither criterion assumes joint
measurability of a two-variable kernel or strong measurability of the
dual-valued map k. Scalar measurability up to null sets follows from the
representation condition. The dominated criterion separately assumes
integrability of its real bound g, rather than measurability of x ↦ ‖k(x)‖.
`HilbertSchmidtEvaluationCriteriaStatement` is exactly their conjunction.

The motivation is the Hilbert–Schmidt step in Getz–Hahn, *An Introduction to
Automorphic Representations* (2024), Lemma 9.3.3, printed pp.247–248
(one-based PDF pp.259–260), in the registered original
`getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
These pages were read directly. The complete October 2026 author errata,
registered as `getz-hahn-2024-errata-2026-10`, SHA-256
`e641ec2a5485443f792935afe5ae4940323755968f784ce290a96d9cd76fc1c2`,
was also read; it contains no entry for Lemma 9.3.3. The arbitrary measure,
independent universes, general Hilbert domain and integrable envelope are
internal derived generalizations, rather than a literal transcription of
that automorphic lemma. A finite Bessel-sum and finite-integral route gives
the desired operator criterion without asserting the jointly measurable
kernel used in its printed proof. The complex inner product follows
Mathlib's convention, conjugate-linear in the first argument.

These targets supply no evaluation family for actual automorphic operators,
quotient measure, finite-volume theorem, smoothing estimate, trace-class
conclusion, convolution factorization or spectral decomposition. Applying
Lemma 9.3.3's final factorization step still needs evaluation estimates for
all relevant test functions and the actual Dixmier–Malliavin theorem.

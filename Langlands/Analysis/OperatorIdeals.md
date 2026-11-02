# Hilbert–Schmidt and trace-class definitions

This module constructs operator predicates and basis sums on actual complex
Hilbert spaces. It supplies definitions for the operator-theoretic part of the
general automorphic program; it proves no cuspidal or operator-ideal theorem.

The source is Getz–Hahn, *An Introduction to Automorphic Representations*
(2024), Definition 9.1.1 and equation (9.3), printed p. 240, PDF p. 252
(one-based). The registered source is
`getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
The October 2026 author errata, registered as
`getz-hahn-2024-errata-2026-10`, SHA-256
`e641ec2a5485443f792935afe5ae4940323755968f784ce290a96d9cd76fc1c2`,
has no correction to this definition. Its five pages were read.

`IsHilbertSchmidt A` means that there exists a Hilbert basis of the domain for
which the real family `‖A (b i)‖²` is summable. The operator is an actual
continuous complex linear map. The existential index is a subset of the domain,
so this predicate does not depend on supplying an external basis-index type.
Mathlib's `exists_hilbertBasis` supplies bases with such index types on every
Hilbert space. The predicate itself does not assume its own summability
conclusion.

`leftModulus A` is the actual continuous functional calculus square root
`CFC.sqrt (A * star A)`. Multiplication is composition and `star A` is the
Hilbert adjoint. This follows the source's **left** modulus convention,
`sqrt(A A*)`. The source also requires positivity when specifying the unique
square root; the construction uses Mathlib's positive square root.

`IsTraceClass A` means that the real diagonal of this left modulus is summable
in some Hilbert basis. The diagonal is
`(inner ℂ (b i) (leftModulus A (b i))).re`. Mathlib's inner product is linear in
the second argument. The placement of the operator in the second argument also
makes `traceIn` the complex diagonal sum with the usual scalar-linear trace
convention. Taking the real part for the positive modulus does not insert an
absolute value or change to the right modulus.

`hilbertSchmidtNormIn b A`, `traceNormIn b A`, and `traceIn b A` are the real
square root of the squared-image sum, the real modulus-diagonal sum, and the
complex operator-diagonal sum, respectively. These are explicitly indexed by a
basis. They use Lean's total `tsum`; without summability, the result can be the
default zero. No convergence or basis independence follows merely by evaluating
these definitions.

The source works with separable Hilbert spaces and endomorphisms. Allowing
arbitrary Hilbert-basis indices and rectangular maps in the Hilbert–Schmidt
predicate and its basis norm is a derived extension of the same formulas.
Trace class and the trace remain endomorphism notions in this module. Finite
bases, zero spaces, and nonseparable spaces are permitted; no spectral theorem
or separability conclusion is asserted for them here.

Basis independence, absolute summability of the trace diagonal for a
trace-class operator, ideal laws, adjoint invariance, compactness, and
trace-class composition of Hilbert–Schmidt operators remain separate proof
obligations. The module supplies no chosen canonical trace or basis-independent
norm before those results are proved. It also supplies no convolution kernel,
cuspidal estimate, discrete decomposition, or automorphic comparison map.

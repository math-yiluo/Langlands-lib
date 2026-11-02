# Hilbert–Schmidt basis-independence target

`Langlands.Analysis.OperatorIdeals.HilbertSchmidtBasisIndependenceStatement`
is a proposition definition, parameterized by complex Hilbert spaces `E`, `F`
and two index types `ι`, `κ`. It quantifies over every continuous complex-linear
map `A : E →L[ℂ] F` and every pair of Hilbert bases `b`, `c` of its domain.
It asserts two conclusions:

1. The nonnegative real family `‖A (b i)‖²` is summable if and only if
   `‖A (c j)‖²` is summable.
2. If the first family is summable, their real sums are equal.

The second conclusion is deliberately conditional on summability: Lean's total
`tsum` has a default value for nonsummable families, which is not the squared
Hilbert–Schmidt norm. No basis, countability assumption, or Hilbert–Schmidt
certificate is an input to the proposition definition itself. Its universally
quantified bases are actual `HilbertBasis` objects. An index type admitting no
such basis imposes no condition; the target is intended to be proved uniformly
for all four universe levels.

The original source is Getz–Hahn, *An Introduction to Automorphic
Representations* (2024), Definition 9.1.1 and (9.3), printed p. 240,
the first paragraph of p. 241, and Exercise 9.1, p. 267. The corresponding
one-based PDF pages are 252, 253 and 279. Registered source
`getz-hahn-2024-automorphic-representations` has SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
The definition, assertion of independence and exercise were directly read.
The complete five-page author errata of October 2026 was also read; its
Chapter 9 corrections on pp. 2–3 do not amend these passages. It is registered
as `getz-hahn-2024-errata-2026-10`, SHA-256
`e641ec2a5485443f792935afe5ae4940323755968f784ce290a96d9cd76fc1c2`.

The source assumes separable Hilbert spaces and states the result for
endomorphisms and their square-root norm. This target is a derived extension
to arbitrary Hilbert-basis indices and rectangular bounded operators. It
states equality of the nonnegative squared sums before taking a square root;
equality of their real square roots follows from equality of these sums.
Summability invariance is made explicit so that an existential definition
using one basis can subsequently be used with any basis. No separability
claim is made for any measure space.

The module imports only Mathlib's Hilbert-basis theory. In particular, it
expresses the prerequisite directly in basis sums and does not import or
resubmit the separately staged operator definitions. Once proved, it can be
applied to the basis sums used there. Relating its conclusion to a particular
existential operator predicate or packaging a canonical norm is a further
implementation step.

This file contains no proof. It makes no assertion about trace-norm or
trace independence, ideal laws, adjoints, compactness, kernels, or automorphic
convolution operators. Those remain separate obligations in the general
automorphic program.

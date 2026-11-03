# A chosen-basis operator trace formula

Worker 116 constructs `operatorTrace A` for an actual bounded complex-linear
endomorphism of an arbitrary complete complex inner-product space. Mathlib's
`exists_hilbertBasis ℂ E` supplies a basis indexed by a subset of E. Classical
choice selects that subset and a Hilbert basis on it; `operatorTrace A` is
`traceIn` in this fixed basis. The selected basis depends on the space and its
structures, rather than on A or a proof that A is trace class. The construction
requires no separability, finite-dimensionality or external index type.

This is a total scalar-valued function on bounded endomorphisms. Its definition
alone gives neither absolute summability nor basis independence. On a
nonsummable diagonal, Lean's total `tsum` can return zero. Consequently no trace
interpretation, additivity or cyclicity outside the trace-class domain is
claimed. Identification with every supplied Hilbert basis for a trace-class
operator, and linearity and bounded cyclicity on that domain, are separate
proposition and proof obligations. The construction imports no such proof.

The formula realizes the trace defined after Getz–Hahn, *An Introduction to
Automorphic Representations* (2024), Definition 9.1.1 and (9.3), printed p.240
(one-based PDF p.252). The source's basis-independence assertion on printed
p.241 and Exercise 9.1 on p.267 justify the intended use after their formal
counterpart is proved. Mathlib's inner product is linear in its second
argument, so the diagonal is `inner ℂ (b i) (A (b i))`; this is the usual complex
linear trace convention. The existing trace-class predicate uses the positive
left modulus `sqrt(A A*)` and is unchanged.

The registered source is `getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
The complete five-page October 2026 author errata, source
`getz-hahn-2024-errata-2026-10`, SHA-256
`e641ec2a5485443f792935afe5ae4940323755968f784ce290a96d9cd76fc1c2`,
has been read and does not amend these passages. The source assumes separable
Hilbert spaces. Choice of a subset-indexed basis on an arbitrary Hilbert space
and the total extension outside trace class are internal implementation
choices extending the source's formula; the source is not claimed to define
this total extension. No automorphic operator, kernel or spectral theorem is
constructed here.

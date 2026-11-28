# Factoring smooth functionals through finitely many genuine derivatives

`smoothDerivativeFunctional` represents a continuous scalar functional on
`DerivativeSmoothVectors` as a bounded functional of finitely many genuine
word derivatives in the original normed representation space.

The derivative seminorm topology bounds the functional by a constant times
the supremum of a finite family of word seminorms. The coordinate map into
the corresponding finite product has kernel contained in the functional's
kernel. Pass to the coordinate range by the quotient-by-kernel equivalence.
The supremum bound makes the resulting form continuous on that subspace,
and complex Hahn–Banach extends it to the full finite product.

The finite-coordinate factor is an internal construction for controlling
mixed functionals on two smooth factors. The use of continuous Whittaker
forms on smooth projective tensor products comes from §2, pp. 8–9 and
Lemma 14.1, p. 106 of the author-posted edition of
[H. Jacquet, *Archimedean Rankin–Selberg Integrals* (2009)](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf#page=8).
The registered source is `jacquet-2009-archimedean-rankin-selberg`, SHA-256
`7a11766eadf25fb7452ce7faa193469791796f572fc654c8fe90a8608bb46afe`.

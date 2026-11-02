# A coefficient neighborhood preserving a simple field extension

This internal construction supports the polynomial approximation step of the
unchanged totally real Galois realization target. It treats arbitrary normed
fields `K,L` in independent universes, with a normed `K`-algebra structure on
`L`. The final stability theorem additionally assumes Mathlib's `IsKrasner K L`,
a separable element `x`, and that the minimal polynomial of `x` and the
perturbed polynomial split in `L`.

`conjugateRadius K x` is the minimum of `1` and the finitely many positive
distances from `x` to its distinct conjugates. In the absence of other
conjugates it is `1`. Its positivity and its upper bound by every distinct
conjugate distance are proved directly from this finite minimum.

Writing `n` for the degree of the minimal polynomial and `A=max(norm(x),1)`,
`coefficientRadius K x` is `(conjugateRadius K x / A)^n/(n+1)`. It is positive.
For integral `x`, the quantitative root bound in Mathlib's continuity theorem
simplifies to `conjugateRadius K x`.

For every monic `g` of degree `n` whose coefficient differences have norm less
than this radius, the continuity-of-roots theorem supplies a root `y` closer
to `x` than every distinct conjugate. Krasner's lemma gives `K(x) ≤ K(y)`.
The minimal polynomial of `y` has degree at most that of `g`; the reverse
finite-dimensional bound therefore forces `K(x)=K(y)`. The conclusion is an
equality of actual intermediate fields inside the specified ambient field,
not merely a nonempty abstract isomorphism type.

The original-source motivation is Henniart (1984), Lemma 3.6 and proof,
printed pages 34–35 (PDF pages 35–36), source `henniart-1984-gl3`, SHA256
`968076c8b63d4a94442c080040b684fe1f71b01a3c0933d111a49745369629f7`.
The source uses sufficiently close defining polynomials and Krasner's lemma.
The explicit radius and generic simple-field comparison here are internal
derived content. The proof uses the pinned Mathlib implementations in
`Analysis/Normed/Field/Approximation.lean` and `Krasner.lean`, then the
intermediate-field degree comparison. Worker 37 read the original cited pages.

This module does not yet choose a rational polynomial with distinct real
roots, number fields, primes, completion isomorphisms or Galois comparisons.
Those remain requirements of the totally real realization theorem. It assumes
splitting in the ambient normed field; for the intended local application an
algebraic closure with the spectral norm supplies splitting and Krasner's
lemma, but that specialization is not asserted here.

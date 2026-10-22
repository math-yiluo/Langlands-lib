# Polynomial growth in archimedean matrix coordinates

For an actual number field `K : Type u` and any natural rank `n`, the namespace
`Langlands.Global.ArchimedeanGL` defines a concrete height on
`InfiniteAdelicGL K n`. This group consists of invertible matrices over the
product of archimedean completions. The published multiplicative homeomorphism
`archimedeanGLCoordinates K n` identifies it with matrix units over the mixed
real and complex coordinate ring.

Write `A(g)` for the matrix of these coordinates. The definition is

```
matrixHeight K n g = max 1 (max ‖A(g)‖ ‖A(g)⁻¹‖).
```

The mixed ring has its finite-product supremum norm. The scope
`Matrix.Norms.Operator` selects the submultiplicative matrix row-sum norm:
the supremum over rows of the sum of the norms of the entries. These are the
norms used in `Langlands.Global.ArchimedeanGL`; the normalized product of local
absolute values on the infinite adele ring is not used here. The definition
includes rank zero, where both matrix norms vanish and the height is one.
There is no positivity assumption on the rank.

## Height and growth properties

The height is at least one, nonnegative, and bounds both displayed norms.
`matrixHeight_inv` proves invariance under inversion by exchanging the two
matrix norms. `matrixHeight_mul_le` proves

```
matrixHeight K n (g * h) ≤ matrixHeight K n g * matrixHeight K n h.
```

The proof applies submultiplicativity of the matrix norm to the product matrix
and to the reversed product of inverses, then combines the bounds using the
maximum. Continuity follows from continuity of the coordinate homeomorphism,
unit evaluation, inversion, norms, and maxima. All these properties are proved
on the actual completion-based group.

`HasPolynomialGrowth K n f` is the proposition

```
∃ C : ℝ, 0 ≤ C ∧ ∃ d : ℕ, ∀ g, ‖f g‖ ≤ C * matrixHeight K n g ^ d.
```

Here `f` is any complex-valued function on the group. Neither continuity nor
smoothness is part of this predicate. The natural exponent may be zero.
`HasPolynomialGrowth.zero` and `.const` give the zero function and every
constant function. Addition uses the sum of the constants and the maximum of
the exponents, since the height is at least one. Complex scalar multiplication
multiplies the growth constant by the scalar's norm.

The theorem `HasPolynomialGrowth.rightTranslate` proves preservation under
`g ↦ f(g * h)`. Given a bound with constant `C` and exponent `d`, the
translated bound uses `C * matrixHeight K n h ^ d` and the same exponent.
Submultiplicativity supplies the estimate. Translation by the inverse proves
`hasPolynomialGrowth_rightTranslate_iff`. The definition
`polynomialGrowthFunctions K n` packages exactly these functions as a complex
submodule; `mem_polynomialGrowthFunctions` exposes its defining predicate.

## Provenance and scope

This is derived construction infrastructure motivated by A. Borel and
H. Jacquet, *Automorphic forms and automorphic representations*, Corvallis
Part I (1979), section 1.2, printed pp.189–190 (one-based PDF pp.184–185).
That source defines a group norm using a Hilbert–Schmidt norm of a
finite-dimensional representation with finite kernel and image closed in its
endomorphism space. Its remark explains how adding the contragredient
representation controls escape toward singular matrices. This motivates the
explicit simultaneous control of the matrix and its inverse here.

The present norm is the specified mixed-coordinate row-sum norm, and the
height also takes a maximum with one. This file does not identify it with the
source's Hilbert–Schmidt norm or prove equivalence of their growth predicates.
That comparison remains a separate obligation. No norm-comparison,
automorphic existence, finiteness, or classification theorem is assumed.
The closure and translation proofs above are implemented directly from the
height estimates.

Registered source: `borel-jacquet-1979-automorphic`.
Original file:
`/home/taskhub/central-library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part I.pdf`.
SHA256:
`3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.

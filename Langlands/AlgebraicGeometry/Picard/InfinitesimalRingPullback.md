# Kernels in actual pullback squares of commutative rings

This internal prerequisite concerns an actual categorical pullback square of
commutative rings in an arbitrary common universe `u`:
`p : R → A`, `q : R → B`, `a : A → C`, and `b : B → C`, with
`a ∘ p = b ∘ q`. It does not assume any leg is surjective.

The second projection restricts to `kernelMap : ker p → ker b`. This is a
nonunital ring homomorphism, and `kernelEquiv` is its associated ring
equivalence. Its underlying map is exactly the restriction of `q`.
The forgetful functor from commutative rings to types preserves limits.
The resulting underlying-set pullback gives injectivity of the kernel map:
the first projections of two kernel elements are both zero, and their
second projections determine equality. For surjectivity, an element
`y ∈ ker b` is lifted from the compatible pair `(0,y)`.

For each positive integer `n`, `ker_fst_pow_eq_bot` proves that
`(ker b)^n = 0` implies `(ker p)^n = 0`. Commutativity of the square gives
`ker p ≤ q⁻¹(ker b)`. The standard ideal-power inequality therefore sends
`(ker p)^n` into `ker q`; positivity also puts that power into `ker p`.
Joint injectivity of the two projections forces every element of the
power to be zero. `ker_fst_isNilpotent` derives the nilpotence statement
by increasing any supplied exponent by one to ensure positivity, including
when a ring is the zero ring.

The constructions and proofs are internal consequences of Mathlib's actual
pullback and ideal-power APIs. They use no external mathematical assertion.
This pair supplies a ring prerequisite for infinitesimal patching. It does
not construct scalar-extension identifications, glue line bundles, prove
the actual Picard-groupoid comparison, or establish representability.

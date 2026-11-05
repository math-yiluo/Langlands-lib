# Coordinates of actual affine base changes

The tensor spectrum comparison identifies the actual scheme pullback of
`Spec A` from `R` to `S` with `Spec(S ⊗[R] A)`, with scalar factor first.
The naturality lemma proves compatibility with every supplied algebra map:
the underlying map of the actual pullback is its tensor map conjugated by
these two spectrum isomorphisms. Both projection identities are checked.

Consequently, closed immersion of that actual pullback map is equivalent to
surjectivity of the tensor coordinate map. When the target coordinate algebra
is a diagonal algebra `R[M]`, the published scalar-extension map
`S ⊗[R] A → S[M]` agrees with the tensor map followed by Mathlib's canonical
monoid-algebra scalar-extension equivalence. Its surjectivity therefore gives
exactly the same actual closed-immersion condition.

This internal comparison derives from the tensor-spectrum pullback universal
property and the canonical monoid-algebra scalar-extension equivalence. It
introduces no lifting hypothesis and applies over arbitrary commutative rings.

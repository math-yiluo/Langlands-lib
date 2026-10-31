# Actual order pullback and the canonical Lie comparison

This is an internal prerequisite derived from the published actual abelian-scheme
base-change functor, its additivity in `RationalBaseChange`, and the canonical Lie
base-change theorem in `LieBaseChangeProof`. The Lie theorem is reused, and its
proof is not changed. No separate original-source translation is claimed.

For arbitrary schemes `S,T` in the same universe, a morphism `b : T ⟶ S`, and
an abelian scheme `B` over `S`, `baseChangeEnd b B` is the ring homomorphism on
actual integral endomorphisms defined by the actual base-change functor. Its
identity, zero, additive and multiplicative laws follow from the functor and its
published additivity. The multiplication convention is the endomorphism-ring
convention, so the composition proof uses the reversed pair of factors.

An action `α : O →+* End B` of an arbitrary ring is pulled back by composition
with this ring homomorphism. Its resulting Lie action is exactly the differential
of the pulled-back endomorphism.

`lieBaseChangeIso b B` selects an isomorphism from the **proved** existence in
`lieBaseChange S`. Its characterization is the published canonical equation:
its forward map followed by the dual of the cotangent base-change map equals
the actual dual-pullback comparison. The cotangent comparison is invertible by
the same published theorem, so its dual is invertible. Cancellation proves
uniqueness of the selected Lie isomorphism.

These are actual constructions over arbitrary bases. The module does not prove
naturality of the canonical comparison in abelian-scheme homomorphisms, nor
assert that the two Lie order actions are intertwined by it. That additional
naturality theorem is needed to identify the determinant of the pulled-back
Lie action with the determinant on the base-changed abelian scheme.

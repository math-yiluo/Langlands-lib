# F₄ Cartan rigidity and an actual root

This internal algebraic unit uses Mathlib's oriented F₄ Cartan matrix. Its only
entry-preserving self-map on the four vertices is the identity. The finite
verification uses ordinary kernel-checked `decide`.

For any four actual roots with exactly these pairings, `isRoot_highest`
constructs an actual root whose coefficients are `(2, 3, 4, 2)`. Beginning with
the first root, reflect at zero-based vertices `1, 2, 1, 3, 2, 1, 0`.
The coefficient vectors are respectively `(1,1,0,0)`, `(1,1,2,0)`,
`(1,2,2,0)`, `(1,2,2,2)`, `(1,2,4,2)`, `(1,3,4,2)`, and
`(2,3,4,2)`. Each arithmetic equality is checked with ordinary `decide`;
`RootReflectionCoefficients.IsRoot.reflect` realizes it by an actual root
reflection.

The theorem asserts existence with those coefficients. It does not need or
assert that the chosen roots form a base, or that the resulting root is highest
for an order. The theorem name identifies the familiar coefficient vector;
the proof is the explicit reflection calculation just described, with no
external classification input.

# Coordinate change of the all-test special-linear Galois presentation

Author: Worker 239.

This internal unit starts from a supplied local group isomorphism `E` over
the spectrum of a field `L/K`. For `P ∈ GL_(n+1)(L)` it constructs a new
local group isomorphism `E′` by
`E′(a)(g) = E(a)(P_a g P_a⁻¹)`, where `P_a` is the coefficient image of `P`
at a cover point `a`. Coefficient naturality of conjugation and of `E`
prove naturality on every test scheme. Coordinates in `E′` are obtained by
conjugating the coordinates in `E` by `P_a⁻¹`.

The discrepancy in the new coordinates is
`Int(P_a⁻¹) ∘ D_σ,a ∘ Int(P_(aσ))`.
Consequently an inner representative `X` changes to
`P⁻¹ X σ(P)`, and an outer representative `X` changes to
`P⁻¹ X θ(σ(P))`, with `θ(Q) = (Q⁻¹)ᵀ`. Here an outer representative means
that inverse transpose is applied first and then conjugation by `X`.
The proofs use the coefficient formula at `aσ` and cancellation in `GL`;
the outer formula also uses the multiplicativity of inverse transpose.
If `X = P σ(P⁻¹)`, the changed discrepancy is the identity on every test.

Finally, any supplied coordinate matrix commuting with `P_a` retains its
coordinates under this change. This will apply to the diagonal matrices of
the split torus once a trivialising matrix respecting the weight blocks is
supplied.

All constructions are derived directly from the existing local-isomorphism,
discrepancy, and natural conjugation APIs. No classification, characteristic
restriction, existence of a trivialising matrix, or final Hermitian
presentation is asserted.

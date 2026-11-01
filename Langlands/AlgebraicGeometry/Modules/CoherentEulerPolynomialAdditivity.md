# Coherent Euler polynomial identities

Let `K : Type u` be a field, `X : Scheme.{u}` an actual scheme, and
`f : X → Spec K` a proper morphism. The coefficient sheaves below are
quasi-coherent and have finite sections on every affine open, as expressed by
`HasFiniteAffineSections`. For an actual line bundle `L` and a natural
truncation `d`, the published `coherentEulerPolynomial f M hM L d` is the
rational Newton polynomial of the actual Euler characteristics of
`M ⊗ L^n`.

`coherentEulerPolynomial_iso` proves equality of these polynomials for an
actual sheaf isomorphism `M ≅ N`. `coherentEulerPolynomial_add` proves
`P₂ = P₁ + P₃` for an actual short exact sequence
`0 → M₁ → M₂ → M₃ → 0`, using the same `L` and `d`.
`coherentEulerPolynomial_zero` proves that the polynomial of a zero sheaf is
zero. These three identities hold for every truncation. They do not require
a support bound, Noetherianness, or separatedness.

The proofs are internal derivations. The already published coherent Euler
sequence identities provide invariance under sheaf isomorphisms, additivity
after twisting the short exact sequence by each actual line-bundle power,
and vanishing for a zero sheaf. Applying the finite Newton transform preserves
the first identity; the companion additive Newton homomorphism proves the
addition and zero identities. Proper coherent cohomology supplies the actual
finite cohomology used by those sequence identities.

For `coherentEulerPolynomial_eq_of_supportDimensionLT`, additionally assume
`X` is Noetherian and separated. If
`HasSupportDimensionLT M (d + 1)` and
`HasSupportDimensionLT M (e + 1)` both hold, the two truncations at `d` and `e`
are the same polynomial. Both evaluate to the same actual Euler sequence at
every natural argument, by the published coherent polynomial evaluation
theorem. Equality on that natural-number tail then implies polynomial
equality by the published rational-polynomial uniqueness theorem.
No ordering of `d` and `e` is required.

These results support coherent-sheaf devissage for the actual line-bundle
Euler polynomial task. They do not prove the positive-dimensional ample
leading-term assertion.

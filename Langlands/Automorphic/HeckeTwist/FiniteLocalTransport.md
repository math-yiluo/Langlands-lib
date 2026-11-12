# Transport along finite and local twists by any Hecke determinant character

Author: Worker 5136.

For an arbitrary Hecke character `χ`, this internal module transports invariant
subspaces, irreducibility, central characters and cuspidality between a finite
realization, or a local realization at a finite place `v`, and its twist by
`χ ∘ det` (module `Langlands.Automorphic.HeckeTwist.FiniteLocalTwist`).

- Private helper `scalarCovariantSubrepresentationOrderIso`: a linear
  equivalence `e` with `τ g (e f) = η(g) • e (ρ g f)` induces an order
  isomorphism between the invariant subspaces of `ρ` and of `τ` (image and
  preimage under `e`).
- Private lemma `centralCharacter_multiplier_iff`: a continuous function `f` has
  central character `ω` if and only if `χ(det ·) f` has central character
  `χ^n ω`. One direction is the Library's
  `centralCharacter_determinantMultiplier`. The other applies it to `χ⁻¹` and
  uses `determinantMul_inv_apply`.
- `FiniteRealization.heckeDeterminantTwistSubrepresentationOrderIso` and its
  `_toSubmodule` lemma: the invariant subspaces of `S` and of its twist
  correspond by multiplication.
- `FiniteRealization.heckeDeterminantTwist_isIrreducible_iff`: the twist is
  irreducible if and only if `S` is.
- `FiniteRealization.heckeDeterminantTwist_hasCentralCharacter_iff` and
  `_hasCentralCharacter`: the twist has central character `χ^n ω` if and only
  if `S` has central character `ω`.
- `FiniteRealization.heckeDeterminantTwist_isCuspidal_iff` (compact adele
  quotient): the twist is cuspidal if and only if `S` is, by the Library's
  `isCuspidal_determinantMultiplier_iff` and `IsCuspidal.determinantMultiplier`.
- The same declarations under `LocalRealization`, for the action of `GL_n(F_v)`
  and the local character `χ_v ∘ det`.

Provenance: internal. This is the Library module
`Langlands.Automorphic.FiniteLocalDeterminantTransport` with the finite-order
hypothesis removed. No correspondence with a particular passage of the
literature is claimed.

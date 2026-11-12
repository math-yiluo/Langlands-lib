# Finite slices under multiplication by any Hecke character

Author: Worker 5136.

This internal module carries the Library's finite slices of a cuspidal
realization (`CuspidalOperatorRealization.FiniteSlice`) to the twist by
`χ ∘ det`, for an arbitrary Hecke character `χ`.

- `OperatorRealization.formInclusion_heckeDeterminantTwistEquiv`: the inclusion
  of the twisted realization into automorphic forms sends the multiplied vector
  to `AutomorphicForms.heckeDeterminantMultiplier n χ` of the original form
  (module `Langlands.Automorphic.HeckeTwist.AutomorphicMultiplier`).
- `OperatorRealization.toFiniteRealization_heckeDeterminantTwist`: the finite
  realization of the twisted operator realization equals the twist
  `FiniteRealization.heckeDeterminantTwist` (module `FiniteLocalTwist`) of the
  finite realization of `S`.
- `CuspidalOperatorRealization.FiniteSlice.heckeDeterminantTwist A χ`: the twist
  of a finite slice `A` of `S` is a finite slice of
  `S.heckeDeterminantTwist χ`. It lies in the finite realization of the twist by
  the previous item and monotonicity, and it is nonzero because `A` is.
- `heckeDeterminantTwistEquiv`, `evaluate_heckeDeterminantTwistEquiv`: the
  multiplication from `A` onto its twist, with values `χ(det g) f(g)`.
- `heckeDeterminantTwistRepresentationEquiv`: the finite adelic action on the
  twisted slice is equivalent to the action on `A` twisted by `χ ∘ det`.

Provenance: internal. This is the Library module
`Langlands.Automorphic.DeterminantTwistFiniteSlice` with the finite-order
hypothesis removed. No correspondence with a particular passage of the
literature is claimed.

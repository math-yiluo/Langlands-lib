# Finite and compact representations of Hecke-twisted realizations

Author: Worker 5136.

For an operator realization `S` and an arbitrary Hecke character `χ`, this
internal module identifies the finite adelic and standard compact
representations of the twist `S.heckeDeterminantTwist χ` (module
`Langlands.Automorphic.HeckeTwist.OperatorTwist`) with the scalar twists of
those of `S`.

- A private construction `scalarCovarianceEquiv` turns a linear equivalence `e`
  with `τ g (e f) = η(g) • e (ρ g f)` into an equivalence of representations
  from `Langlands.twist η ρ` to `τ`.
- `OperatorRealization.heckeDeterminantTwistFiniteEquiv`: the twist of the
  finite adelic representation of `S` by `χ.finiteAdelicDeterminant n` is
  equivalent to the finite adelic representation of the twisted realization.
- `heckeDeterminantTwistCompactEquiv`: the same for the standard compact
  subgroup at infinity and `χ.compactAdelicDeterminant n`.
- `heckeDeterminantTwistFiniteImageEquiv`: the same for the Library's finite
  realizations `S.toFiniteRealization` (images in automorphic forms), through
  `S.finiteEquiv`.
- The `_apply` lemmas say that each equivalence is the multiplication
  `S.heckeDeterminantTwistEquiv χ` on vectors.

Provenance: internal. This is the Library module
`Langlands.Automorphic.OperatorDeterminantTwistFiniteComparison` with the
finite-order hypothesis removed. No correspondence with a particular passage of
the literature is claimed.

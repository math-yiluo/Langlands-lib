# Spherical vectors under multiplication by any Hecke determinant character

Author: Worker 5136.

Let `S` be a local realization of `GL_{r+1}(F_v)` at a finite place `v`, and let
`χ` be an arbitrary Hecke character whose local determinant character
`χ_v ∘ det` (the Library's `χ.finiteLocalDeterminant (r + 1) v`) is trivial on
`GL_{r+1}(𝒪_v)` (hypothesis `hlocal`). This internal module compares the
spherical vectors and the standard spherical Hecke operators of `S` and of its
twist `S.heckeDeterminantTwist χ` (module
`Langlands.Automorphic.HeckeTwist.FiniteLocalTwist`).

- Private helpers: `twistFixedEquiv` identifies the `K`-fixed vectors of a
  representation with those of any representation equivalent to its twist by a
  character trivial on `K`. `sum_covariance` and `map_scalar_eigen` are
  elementary rewriting lemmas.
- A private lemma shows that `χ_v ∘ det` is trivial on the Library's spherical
  subgroup, because that subgroup is `GL_{r+1}(𝒪_v)`
  (`localIntegral_eq_sphericalSubgroup`).
- `heckeDeterminantTwistSphericalEquiv`: multiplication restricts to a linear
  equivalence between the spherical vectors of `S` and those of the twist. Its
  `_val` lemma says it is the multiplication on vectors.
- Private lemmas: each standard Hecke operator is the sum of the action of the
  Library's coset representatives (`standardHecke_cornerAction_eq_sum`). On
  every representative, `χ_v ∘ det` takes its value at the standard diagonal
  matrix `standardDiagonal … r i`, because each representative lies in the
  double coset of that matrix.
- `standardHeckeOperator_heckeDeterminantTwist`: on the twist, the `i`-th
  standard Hecke operator applied to the image of a spherical vector `f` is
  `χ_v(det t_i)` times the image of the `i`-th standard Hecke operator applied
  to `f`, where `t_i` is the standard diagonal matrix.
- `standardHeckeOperator_heckeDeterminantTwist_eigen`: an eigenvector with
  eigenvalue `c` maps to an eigenvector with eigenvalue `χ_v(det t_i) · c`.

Provenance: internal. This is the Library module
`Langlands.Automorphic.LocalSphericalDeterminantTwist` with the finite-order
hypothesis removed. No correspondence with a particular passage of the
literature is claimed.

# Affine group isomorphisms descend along cofiltered limits

Worker 875.

`Langlands.GroupScheme.Descent.AffineLimit.isomorphismModel` chooses an actual
level and an isomorphism of group schemes at that level from an isomorphism
over a supplied cofiltered affine limit. The base and every diagram level are
affine schemes, the index category is small in the same universe, and both
groups are affine and locally of finite presentation over the base. The cone
is supplied with its limiting property and a compatible structural map to the
base. No noetherian, flatness, smoothness or étaleness hypothesis is used.
The chosen isomorphism need not recover the specified isomorphism at the limit;
the result asserts existence at a level.

The paired theorems implement the following internal finite-data argument.

- `exists_level_map_eq` gives the affine-source result over an affine base.
  `exists_level_map_eq_of_quasiCompact` descends equality of two fixed maps whose source is
  quasi-compact over the base and whose target is locally of finite type. It also records that the
  equality holds at every level mapping to the chosen one. This uses Mathlib's
  finite-type equality theorem on the actual base-change limit cone.
  Worker 668 generalized the source hypothesis to quasi-compactness for
  descent of the centrality equation on the product of two groups.
- `exists_level_isMonHom` applies that equality theorem to preservation of the
  unit and multiplication. A common cofiltered refinement satisfies both
  equations, so the map there is a homomorphism of group schemes.
- `exists_level_isIso` applies the published affine scheme isomorphism descent
  theorem, exchanging the two pullback factors to match the slice convention.
  `isIso_pullback_of_comp` records preservation under further base change and
  transport along an equal composite.
- `exists_level_groupIso` first factors the underlying limit map through one
  level using local finite presentation. The pullback comparison proves that
  this factorization becomes the original group isomorphism at the limit.
  Restricting the diagram to levels over the chosen one preserves its limit,
  since the forgetful functor from the over category is initial. The preceding
  two results descend the homomorphism equations and invertibility. A common
  refinement is an actual group-scheme isomorphism; the standard iterated
  pullback comparisons put it over the corresponding original diagram level.
  `isomorphismModel` chooses this result.

This is an internal consequence of the published group-scheme base-change
comparisons, `Langlands.AlgebraicGeometry.AffineLimit.exists_isIso_baseChangeMap`,
Mathlib's affine-transition limit factorization and equality theorems, and
initiality of the over-category forgetful functor for cofiltered categories.
It supplies a generic spreading step. It does not construct a strict
henselization or prove the host multiplicative-type fpqc extension theorem.

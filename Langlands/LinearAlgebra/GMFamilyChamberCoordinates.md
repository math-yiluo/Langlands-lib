# Obtuse simple roots and chamber coordinates

Module `Langlands.LinearAlgebra.GMFamilyChamberCoordinates` proves two facts
about the simple roots of a chamber `P ∈ parabolics R a` of a Levi space `a`
that the proof of Lapid's Lemma 8
(`Langlands.LinearAlgebra.GMFamilyOrthogonalSetLimitProof`) uses to turn the
hypothesis `⟪v, Y_P⟫ ≥ t` into decay.

## Results

- `coeff_nonneg_of_obtuse`: if `v_i` is a linearly independent family of
  vectors with `⟪v_i, v_j⟫ ≤ 0` for `i ≠ j`, and `⟪v_j, ∑ c_i v_i⟫ ≥ 0` for
  all `j`, then all `c_i ≥ 0`. Proof: write `c = p − m` with `p, m ≥ 0` of
  disjoint supports, `w_± = ∑ p_i v_i, ∑ m_i v_i`. Then
  `0 ≤ ⟪w_-, w_+ − w_-⟫` by hypothesis and `⟪w_-, w_+⟫ ≤ 0` by obtuseness, so
  `‖w_-‖² ≤ 0`, `w_- = 0` and `m = 0` by independence.
- `positiveSimpleRoots_inner_nonpos`: the indecomposable positive roots at a
  regular point `h` are pairwise obtuse. If `⟪x, y⟫ > 0` then `x − y` is a
  root (`IsRootSet.sub_mem_of_inner_pos`), and according to its sign at `h`
  either `x` or `y` is decomposable.
- `simpleRoots_inner_nonpos`: the vectors `simpleRoots a P` are pairwise
  obtuse. By `simpleRoots_posSet_eq_image` they are the orthogonal projections
  to `a` of the ambient simple roots of a regular ambient chamber above `P`
  that do not vanish on `a`, and `aᗮ` is spanned by the ambient simple roots
  vanishing on `a` (`leviSpaceOf_eq_orthogonal_span_active`). For ambient
  simple roots `x ≠ y`, the component `z = y − pr_a(y)` lies in `aᗮ` and has
  nonpositive inner products with the vanishing simple roots, so by
  `coeff_nonneg_of_obtuse` it is a combination of them with nonpositive
  coefficients. Hence `⟪x, z⟫ ≥ 0` and
  `⟪pr_a x, pr_a y⟫ = ⟪x, y⟫ − ⟪x, z⟫ ≤ 0`.
- `chamberVector`, `chamberBasis`: the simple roots of `P` as a basis of
  `relativeSpace R a = 𝔞_M^G`, from `linearIndependent_simpleRoots` and
  `span_simpleRoots_eq`; `chamberBasis_apply` gives its vectors.
- `exists_chamber_coord_lower`: there is `c > 0` such that every
  `y ∈ relativeSpace R a` with `⟪v, y⟫ ≥ t ≥ 0` for all `v ∈ simpleRoots a P`
  has all its coordinates in `chamberBasis` at least `c t`. Proof: let `ρ` be
  the vector with `⟪v, ρ⟫ = 1` for all simple roots `v`
  (`exists_inner_values`). Its coordinates `r_i` are nonnegative by
  `coeff_nonneg_of_obtuse`, and positive since `⟪v_i, ρ⟫ = 1` would otherwise
  be a sum of nonpositive terms. Take `c = min r_i` if `P` has simple roots,
  and `c = 1` if `simpleRoots a P` is empty (then there are no coordinates and
  the claim is vacuous). The coordinates of `y − tρ` are nonnegative by
  `coeff_nonneg_of_obtuse`, so the coordinates of `y` are at least
  `t r_i ≥ c t`.

## Provenance

The obtuseness of simple roots is a standard fact about root systems; the
coordinate bound is the elementary linear algebra behind Lapid's use of (15),
E. Lapid, *On Arthur's asymptotic inner product formula of truncated
Eisenstein series*, Clay Math. Proc. 13 (2011), §7, pp. 326–327
(`lapid-2011-asymptotic-inner-product-truncated-eisenstein`, volume PDF
SHA-256 `760161175f57a28d2e05de1f5638bc205d33123ae95f67ce4296b4b651fa950b`).
The proofs here are derived directly from the root-set axioms and the Library
modules `GMFamilyLeviRootBasis` and `GMFamilySplittingGeometry`.

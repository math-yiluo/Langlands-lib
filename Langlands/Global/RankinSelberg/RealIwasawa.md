# The Iwasawa decomposition of `GL_n(ℝ)` with continuous coordinates

Helper module for the convergence part of the real local Rankin–Selberg theory (towards
`Langlands.Global.RankinSelbergGlobal.RealPlaceFunctionalEquationStatement`).
All declarations are proved; there are no hypotheses or axioms.

All declarations are in the namespace
`Langlands.Global.RankinSelbergGlobal.RealIwasawa`. Throughout, `G = GL_n(ℝ)` is the
Library's `Langlands.GeneralLinear n ℝ`, `K = unitaryCompact ℝ n` is the orthogonal group,
`N = upperUnipotent n ℝ` is the upper unipotent subgroup, and `A` is the group of positive
diagonal matrices, parametrized logarithmically by `ℝⁿ`.

## Upper triangular matrices with positive diagonal

- `IsPosUpper b`: `b` is upper triangular with positive diagonal entries.
- `upper_mul_diag`: the diagonal of a product of upper triangular matrices is the product
  of the diagonals. `IsPosUpper.mul`, `isPosUpper_inv`: the property is stable under
  products and inverses.
- `eq_one_of_isPosUpper`: an orthogonal matrix that is upper triangular with positive
  diagonal is the identity (its inverse, the transpose, is both upper and lower
  triangular; the diagonal entries square to one and are positive).
- `exists_isPosUpper_mul_orthogonal`: every invertible real matrix is `b k` with `b`
  upper triangular with positive diagonal and `k` orthogonal. Proved from the Library's
  `LinearAlgebra.TriangularUnitary.exists_upperTriangular_mul_unitary` by moving the signs
  of the diagonal of the triangular factor into the orthogonal factor with a diagonal sign
  matrix.

## The orthogonal coordinate `kpart`

- `kpart g : K` is a chosen orthogonal element with `IsPosUpper (g (kpart g)⁻¹)`
  (`isPosUpper_mul_kpart_inv`).
- `eq_of_isPosUpper`, `kpart_eq`: it is unique: if `g k₁⁻¹` and `g k₂⁻¹` are both upper
  triangular with positive diagonal, then `k₂ k₁⁻¹` is orthogonal and upper triangular
  with positive diagonal, hence the identity.
- `continuous_kpart`: `kpart` is continuous. Its graph is the closed set of pairs
  `(g, k)` such that `g k⁻¹` is upper triangular with nonnegative diagonal (nonnegative
  entries of an invertible triangular matrix are positive, `diag_ne_zero`), and a map into
  a compact Hausdorff space with closed graph is continuous
  (`continuous_of_isClosed_graph`).

## The torus and the remaining coordinates

- `torus y = diag(exp y₁, …, exp yₙ)` as an element of `G`, with `torus_val`,
  `torus_add` (`torus (y + z) = torus y * torus z`), `torus_zero`, `torus_neg`,
  `continuous_torus`, `isPosUpper_torus`.
- `bpart g = g (kpart g)⁻¹`, upper triangular with positive diagonal
  (`isPosUpper_bpart`), with `bpart g * kpart g = g`.
- `alpha g : ℝⁿ`, the logarithms of the diagonal entries of `bpart g` (`exp_alpha`).
- `npart g : N`, the element `bpart g * torus (-alpha g)`, which is upper triangular with
  diagonal entries one (`npart_mem`).
- `npart_mul_torus_mul_kpart`: the Iwasawa decomposition
  `g = npart g * torus (alpha g) * kpart g`.
- `kpart_iwasawa`, `bpart_iwasawa`, `alpha_iwasawa`, `npart_iwasawa`: for `u ∈ N`,
  `y ∈ ℝⁿ`, `k ∈ K`, the coordinates of `u * torus y * k` are `k`, `u * torus y`, `y`
  and `u`. So the decomposition is unique.

## Equivariance

- `alpha_mul_unitary`, `npart_mul_unitary`: `alpha` and `npart` are right
  `K`-invariant.
- `alpha_unipotent_mul`, `npart_unipotent_mul`: for `h ∈ N`,
  `alpha (h g) = alpha g` and `npart (h g) = h * npart g`.
- `conjTorus z u = torus z * u * torus (-z)`, again in `N` (`conjTorus_mem`).
- `torus_mul_eq`, `alpha_torus_mul`, `npart_torus_mul`: left multiplication by
  `torus z` gives `alpha (torus z * g) = z + alpha g` and
  `npart (torus z * g) = conjTorus z (npart g)`.

## Continuity and descent to `N \ G`

- `continuous_bpart`, `continuous_alpha`, `continuous_npart`, `continuous_conjTorus`.
- `alphaQ`: since `alpha` is left `N`-invariant, it descends (Library
  `QuotientIntegration.descend`) to the coset space
  `LeftQuotient N = Quotient (QuotientGroup.rightRel N)`; `alphaQ_mk` holds by
  definition and `continuous_alphaQ` follows from the quotient topology.
- `alpha_torus_mul_unitary`: `alpha (torus y * k) = y`.
- `mk_eq_mk_torus_mul_kpart`: the class of `g` is the class of
  `torus (alpha g) * kpart g`.
- `alphaQ_preimage`: the preimage under `alphaQ` of `C ⊆ ℝⁿ` is the image of `C × K`
  under `(y, k) ↦ [torus y * k]`. With `continuous_mk_torus_mul`, this gives
  `isCompact_alphaQ_preimage`: preimages of compact sets are compact.

## Provenance

The Iwasawa decomposition `G = N A K` of `GL_n(ℝ)` with unique, continuous coordinates is
standard (Gram–Schmidt; see e.g. Jacquet, *Archimedean Rankin–Selberg integrals*, 2009,
section 3, where integrals over `N \ G` are written in these coordinates). The Lean route
(existence from the Library's triangular–unitary factorization, uniqueness from
`eq_one_of_isPosUpper`, continuity of `kpart` from the closed graph theorem for maps into a
compact space) is internal.

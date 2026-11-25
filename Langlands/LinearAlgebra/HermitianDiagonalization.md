# Orthogonal bases for Hermitian forms

The module `Langlands.LinearAlgebra.HermitianDiagonalization` proves that a Hermitian form over a
field of characteristic different from two has an orthogonal basis, isotropic vectors allowed, and
the matrix form: Hermitian matrices are congruent to diagonal ones.

## Content

Let `E` be a field with `2 ≠ 0`, `c : E →+* E`, and `B` a form on a finite-dimensional
`E`-vector space, linear in the first variable and `c`-semilinear in the second
(`B : V →ₗ[E] V →ₛₗ[c] E`), Hermitian: `c (B x y) = B y x`.

- `eq_zero_of_apply_self_eq_zero` (polarization): if `B x x = 0` for all `x` then `B = 0`; so a
  non-zero `B` has a vector with `B x x ≠ 0` (`exists_apply_self_ne_zero`).
- `exists_orthogonal_basis_of_hermitian`: `B` has an orthogonal basis, indexed by any finite type
  of cardinality `dim V`. Induction on the dimension: take `x` with `B x x ≠ 0`; the kernel of
  `y ↦ B y x` is a complement of `E x`, and an orthogonal basis of it together with `x` is one of
  `V`.
- `exists_congr_diagonal_of_hermitian`: for an involution `c` and a square matrix `G` with
  `c (G a b) = G b a`, there are `P` with `det P ≠ 0` and `d` with `Pᵀ G c(P) = diag d`, the entries
  `d i` fixed by `c`, and non-zero when `det G ≠ 0`. Apply the theorem above to the form
  `(x, y) ↦ x ⬝ G c(y)` and take for the columns of `P` an orthogonal basis.

The Library's `Langlands.Sesquilinear.exists_orthogonal_basis`
(`Langlands/GroupScheme/Examples/HermitianRootDiagonalization.lean`) proves the same for an
anisotropic reflexive form (`B x x = 0 → x = 0`), in every characteristic, with the semilinearity
in the other variable; the theorem here allows isotropic vectors and needs `2 ≠ 0`. Both are kept.

The matrix form is used for the unitary groups of `Langlands/Group/Unitary/Basic.lean`
(`IsQuadraticInvolution.exists_eq_mul_diagonal_mul`), and through them for the Gauss integrals of
Hermitian forms of `Langlands/Theta/DualPair/Unitary/`.

## Source and licence

From <https://github.com/leanprover-community/riemann-hypothesis>, commit `f1f6d65`:
`src/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsOrthogonalBasisDotProductApplyEq.lean`,
lines 12–105 and 130–220. The repository has no licence file; the text is used with attribution, see `licenses/RiemannHypothesis/SOURCE.md`.

## Changes against the source

- Namespace `GlobalTheory.HermDiag` → `Langlands.Sesquilinear` (public) and
  `Langlands.Sesquilinear.HermitianDiagonalization.Internal`.
- Renamed: `exists_orthogonal_basis` → `exists_orthogonal_basis_of_hermitian` (the unqualified
  name is the Library's anisotropic theorem), `exists_congr_diagonal` →
  `exists_congr_diagonal_of_hermitian`. The other lemmas are internal.
- Not taken: the variants with a prescribed first vector (`exists_orthogonal_basis_apply_eq`,
  `exists_orthogonal_basis_dotProduct_apply_eq`, `exists_congr_diagonal_col_eq`, lines 107–129 and
  222–237) and the section on CM fields (lines 239–268), which the unitary block does not use;
  the source's import of `ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature`
  is dropped with them.

## Declarations

- `Langlands.Sesquilinear.eq_zero_of_apply_self_eq_zero`
- `Langlands.Sesquilinear.exists_apply_self_ne_zero`
- `Langlands.Sesquilinear.exists_orthogonal_basis_of_hermitian`
- `Langlands.Sesquilinear.exists_congr_diagonal_of_hermitian`

## Dependencies

Mathlib: `LinearAlgebra.Basis.Fin`, `LinearAlgebra.Dimension.Finite`,
`LinearAlgebra.FiniteDimensional.Lemmas`, `LinearAlgebra.Matrix.SesquilinearForm`,
`LinearAlgebra.Matrix.ToLinearEquiv`, `LinearAlgebra.Matrix.Basis`, `Tactic.LinearCombination`.

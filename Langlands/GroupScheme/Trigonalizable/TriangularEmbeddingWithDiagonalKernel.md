# Closed triangular embeddings with diagonal kernel a given unipotent subgroup

Module `Langlands.GroupScheme.Trigonalizable.TriangularEmbeddingWithDiagonalKernel`, namespace
`Langlands.GroupScheme.TrigonalizableFlag`.

This module turns the triangularization of `StableFlag` into a closed
embedding of `G` into the Library's upper triangular group scheme whose actual
diagonal kernel is exactly the given unipotent subgroup. This is Milne's
Proposition 16.2 (d) ⇒ (c), with the kernel identified.

## Notation

`k : Type u` is a field, `N : ℕ`, and the weights `a ↦ -(a.val : ℤ)` on
`Fin N` make the Library's `GeneralLinear.blockParabolicScheme (Fin N) k _` the
upper triangular group scheme `B_N`, `blockLeviScheme` the diagonal torus and
`blockLimitHom : B_N ⟶ blockLeviScheme` the diagonal projection.

## Declarations

- `exists_closed_blockParabolic_factor`: a closed representation
  `ρ : MatrixRepresentation G (Fin N)` whose matrix at the universal point
  `ρ.pointMatrix G.X (𝟙 G.X)` has zero entries below the diagonal factors as
  `j ≫ blockParabolicHom = ρ` with `IsClosedSubgroup j`. This adapts the
  published `exists_closed_blockParabolic_factor_of_rational` (which tests
  rational points of smooth groups) to the universal point itself.
- `mem_range_kernelι_diagonal_iff`: for `j : G ⟶ B_N`, a point `x` of `G`
  lies in the range of the actual kernel of `j ≫ blockLimitHom` if and only if
  the matrix of `x` under `j ≫ blockParabolicHom` agrees with the identity at
  all entries `(a, b)` with `b ≤ a`. It is assembled from the published
  `TriangularLayer.filtration_zero_eq_diagonal_kernel`,
  `mem_range_filtrationHom`, `refinedW_zero` and
  `W_zero_eq_blockUnipotentSubgroup`.
- `exists_triangular_embedding`: let `G` be affine and locally of finite
  type, `U` affine with `IsUnipotent U`, `i : U ⟶ G` with normal range,
  `Λ` finitely generated and `q : G ⟶ D(Λ)` with
  `RelativeRoot.IsFppfQuotient (range i) q`. Then there are `N` and
  `j : G ⟶ B_N` with `IsClosedSubgroup j` and
  `range (kernelι (j ≫ blockLimitHom)) = range i`.

## Proof of `exists_triangular_embedding`

The published `affineLinearEmbeddingStatement` gives a closed representation
`ρ₀`. `exists_triangular` gives `g` such that `ρ = ρ₀.conjugate (basePoint g)`
is upper triangular on every test with diagonal `1` on `U`; `ρ` is still a
closed subgroup (composition with the inner automorphism isomorphism). The
first declaration gives the closed `j`.

For the kernel, `⊇`: for a point `h ≫ i` of `U` the matrix of `ρ` is zero
below the diagonal and `1` on it, so `mem_range_kernelι_diagonal_iff` applies.
For `⊆`: the actual kernel `K` of `j ≫ blockLimitHom` is unipotent by the
published `isUnipotent_kernel_comp_of_closedSubgroup`, applied with
`unipotentClosedSubgroup`, `unitriangularUnipotent` and
`blockUnipotentIsoKernel`. `D(Λ)` is of multiplicative type (split by `k`
itself through `Diagonalizable.baseChangeIso`). Part 3 of the published
`unipotentMultiplicativeTriviality` (Milne 14.17–14.18) says that
`kernelι _ ≫ q : K ⟶ D(Λ)` has trivial range. So every point of `K` maps to
`1` in `D(Λ)`, hence lies in `range (kernelι q) = range i`.

## Source and provenance

J. S. Milne, *Algebraic Groups* (2017), `milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`, printed
pages (PDF page = printed page + 16):

- Proposition 16.2, pp.324–325, (b) ⇒ (c): "Apply (b) to a faithful
  finite-dimensional representation of G (which exists by 4.9), and use that
  every monomorphism is a closed immersion (3.35)."
- Proof of Theorem 16.21, p.330: "Let U be a unipotent subgroup of G. Then
  q(U) is unipotent and diagonalizable, hence trivial. Therefore
  U ⊂ G ∩ U_n, and so G ∩ U_n is the largest unipotent subgroup G_u of G."

The Lean theorem is derived: it records, for the given `U` and `q`, the
identification `G ∩ U_n = U` of the actual scheme kernels on every test. The
inclusion `U ⊆ G ∩ U_n` comes from the construction of the basis rather than
from the maximality argument quoted above; the reverse inclusion is the
quoted argument. No smoothness, connectedness, algebraic closure or
characteristic hypothesis is used.

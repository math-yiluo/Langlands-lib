# Triangular ambient representations of solvable subgroups

For a homomorphism `i : H ⟶ G` over a field `k : Type u`,
`SolvableSubgroupTriangularRepresentation i` consists of a natural number `N`,
a closed faithful representation `ρ : G ⟶ GL_N`, a closed embedding
`j : H ⟶ B_N` in the concrete upper triangular group, and the equality
`j ≫ B_N_ι = i ≫ ρ`. Here `B_N` is the existing block parabolic with weights
`j ↦ -(j.val : ℤ)`.

`IsSolvableGroupScheme.ambientTriangularRepresentation` constructs these data
over an algebraically closed field. It assumes that `G` is smooth and affine,
that `H` is smooth, affine, connected and solvable, and that `i` is closed.
It restricts the existing closed faithful representation of `G` to `H`, applies
`lieKolchinRationalTriangularization`, and conjugates the ambient representation
by the resulting change of basis. The published theorem
`MatrixRepresentation.exists_closed_blockParabolic_factor_of_rational` gives the
closed triangular factor. Closedness is preserved under the ambient inner
automorphism and composition with `i`. Normality of `H` is not required.

`MatrixRepresentation.diagonal_eq_of_charpoly_of_retraction` is an algebraic
helper. Let `B` and `C` be upper triangular matrices with equal characteristic
polynomials over any commutative domain, indexed by a finite linearly ordered
type. Let `p` be a ring endomorphism fixing every `B i i` and satisfying
`p (C i i) = B i i`. Then `C i i = B i i` for each index. No injectivity or
idempotence of `p` is assumed. The proof evaluates the factored characteristic
polynomials at `C i i`. The factor indexed by `i` on the `C` side vanishes,
so some `C i i - B j j` is zero. Applying `p` identifies `B j j` with `B i i`,
which proves the conclusion. Empty index types are included.

This is internal derived content, with provenance in the imported Library
representation and Lie–Kolchin constructions and Mathlib's triangular
characteristic polynomial formula. These data and the diagonal lemma are
prerequisites for a normal-solvable centrality argument; this module does not
prove centrality or positive-root uniqueness.

# Simultaneous triangularization of a cyclic matrix group

Supporting module of Task 5003 (module `Langlands.Automorphic.AssociatedGammaTriangular`,
namespaces `Langlands.LieKolchin` and `Langlands.Weil.Local`). At unramified places the local restriction of a relative
Weil representation is determined by one Frobenius operator. The published
`PrincipalSeriesPairGammaMatchStatement` asks for a basis in which every Weil element acts by an
upper triangular matrix; this module provides that basis in matrix form. Standard linear algebra.

## Results

- `exists_mulVec_eigenvector_cyclic`: a homomorphism `ρ : Multiplicative ℤ →* M_(n+1)(ℂ)` has a
  common eigenvector. Take an eigenvector `v` of the generator `A = ρ(1)` (`exists_eigenvalue`,
  `ℂ` algebraically closed). `ρ(-1)` is a left inverse of `A`, so the eigenvalue `c` is nonzero
  and `ρ(-1) v = c⁻¹ v`. Integer induction then gives an eigenvalue for every element.
- `exists_triangularizing_cyclic`: every `ρ : Multiplicative ℤ →* M_n(ℂ)` admits mutually inverse
  `P`, `Q` such that every `Q ρ(g) P` is upper triangular. The proof is the induction of the
  published `LieKolchin.exists_triangularizing` (same block lemmas `stepP`, `stepQ`, `ext1`),
  with the cyclic common eigenvector in place of the connected-solvable one.

## Unramified local Weil representations (namespace `Langlands.Weil.Local`)

- `representation_eq_frobenius_zpow`: if a representation `ρ` of the local Weil group is trivial
  on the inertia subgroup, then `ρ g = ρ(Fr)^(deg g)` for every `g`, where `Fr` is the geometric
  Frobenius `localGeometricFrobenius K`, `deg g = localDegreeInt K g`, and the power is taken in
  the unit group of `End V`. Proof: `Fr^(-deg g) * g` has degree zero, so it lies in the
  inertia subgroup, and `ρ` is multiplicative.
- `exists_triangular_basis`: if `finrank V = n` and `ρ` is unramified, there are a basis `b`
  of `V` indexed by `Fin n` and units `d_i` such that for every Weil element `g`, the matrix of
  `ρ g` in `b` is upper triangular (`b.repr (ρ g (b j)) i = 0` for `j < i`) with diagonal
  entries `d_i ^ (deg g)`. Proof: apply `exists_triangularizing_cyclic` to
  `k ↦ toMatrix(ρ(Fr)^k)`, take `b` to be the image of the reference basis under the linear
  equivalence with matrices `P`, `Q`, and read off the diagonal. In a product of upper
  triangular matrices, the diagonal is multiplicative, so `k ↦ (Q ρ(Fr)^k P)_ii` is a
  homomorphism from `Multiplicative ℤ`, and `d_i` is its value at `1`.
- `eulerPolynomial_of_triangular`: if the matrix of `A` in a basis `b` indexed by `Fin n` is
  upper triangular, then `det(1 - X A) = ∏_i (1 - a_ii X)`, where `a_ii` are the diagonal
  entries. Proof: `LocalFactor.eulerPolynomial_eq_det` and `Matrix.det_of_isUpperTriangular`.
- `localDegreeInt_localGeometricFrobenius`: the geometric Frobenius has degree `1`.
- `Langlands.Unramified.Eigenvalues.exists_perm_of_ofTuple_eq`: two tuples of nonzero complex
  numbers with the same unordered spectrum differ by a permutation: `d i = z (σ i)`. The
  fibres of `d` and `z` over each value have the same cardinality (multiset counts), and
  `Equiv.ofFiberEquiv` glues bijections between them.
- `exists_triangular_basis_of_eulerPolynomial`: suppose `ρ` is unramified and
  `det(1 - X ρ(Fr)) = ∏_i (1 - z_i X)`. Then there are a basis `b` and a permutation `σ` such
  that every `ρ g` is upper triangular in `b`, with diagonal entries `z_(σ i) ^ (deg g)`.
  Proof: by `exists_triangular_basis` the diagonal entries are `d_i ^ (deg g)`. At `g = Fr`,
  `eulerPolynomial_of_triangular` gives `∏ (1 - d_i X) = ∏ (1 - z_i X)`. Injectivity of the Euler
  polynomial on unordered spectra (`Eigenvalues.eulerPolynomial_injective`) and
  `exists_perm_of_ofTuple_eq` then give `σ`.

The geometric Frobenius degree identity reuses `Langlands.Weil.Local.localDegreeInt_localGeometricFrobenius` from [DegreeFrobenius](../Weil/Local/DegreeFrobenius.md).

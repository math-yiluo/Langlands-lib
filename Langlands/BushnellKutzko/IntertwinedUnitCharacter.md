# Determinant factorization of intertwined unit characters

Bushnell–Kutzko, *The admissible dual of GL(N) via compact open subgroups*
(1993), (2.4.11), printed pp. 72–73 and 78 (PDF pp. 84–85 and 90).
Literature ID `bushnell-kutzko-1993-admissible-dual-gln`, SHA-256
`811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.

The theorem `intertwinedUnitCharacter` proves
`IntertwinedUnitCharacterStatement` at all universe levels. Let `L` be a
lattice chain in a vector space `V` over a nonarchimedean local field `F`,
let `k ≥ 1`, and let `χ : U^k(L) →* ℂˣ` be intertwined by every unit of
`End_F(V)`. BK93 states (2.4.11) for smooth characters. The proof below
uses no continuity, so it applies to every homomorphism into `ℂˣ`.
The private lemma `character_kills_determinant_kernel` shows that `χ` is
trivial on the elements of determinant one. The private theorem
`factorsThroughDet` then builds the factorization.

**Matrix coordinates.** The proof fixes a uniformizer `π` and a basis of
`V` splitting `L` (`LatticeChain.exists_basis_splits`). It transports
`U^k(L)` along the matrix isomorphism of this basis to a subgroup `H` of
`GL_d(F)`. The transport preserves determinants. The intertwining
hypothesis becomes the following: for every `s` in `GL_d(F)`, `χ` takes
the same value on `v` and `s v s⁻¹` whenever both lie in `H`. A matrix
`1 + x` lies in `H` exactly when the endomorphism with matrix `x` lies in
`𝔓^k(L)` (`k ≥ 1`). For `v ∈ H` and any coordinates `i`, `j`, the
elementary endomorphism `E_{ij}` with the single entry `(v - 1)_{ij}`
equals `E_{ii}(1) (v - 1) E_{jj}(1)`. It lies in `𝔓^k(L)` because
`E_{ii}(1)` lies in `𝔓^0(L)` for a splitting basis
(`elementaryEnd_diag_mem_order`).

**Diagonal entries.** For `v ∈ H`, `E_{ii}(v_{ii} - 1)` lies in `𝔓^1(L)`.
Its trace `v_{ii} - 1` therefore lies in the maximal ideal
(`trace_mem_maximalIdealInField`). So every diagonal entry `v_{ii}` is a
unit of the valuation ring.

**Transvections.** Let `i ≠ j` and let the transvection `T_{ij}(a)` lie
in `H`. Since `π - 1` is a unit of the valuation ring, `b = a / (π - 1)`
also gives `T_{ij}(b)` in `H`, and `π b = b + a`. Conjugating `T_{ij}(b)`
by the diagonal matrix that scales coordinate `i` by `π` gives
`T_{ij}(b + a) = T_{ij}(b) T_{ij}(a)`. Intertwining gives
`χ(T_{ij}(b)) = χ(T_{ij}(b)) χ(T_{ij}(a))`, so `χ(T_{ij}(a)) = 1`.

**Elimination.** For `v ∈ H` and `i ≠ j`, left multiplication by
`T_{ij}(-v_{ij} / v_{jj})` clears the entry `(i, j)` and changes only
row `i`. This transvection lies in `H` because `v_{jj}` is a unit of the
valuation ring. The step preserves the value of `χ` and the determinant.
It adds a multiple of row `j` to row `i`. A column `c ≠ j` whose
off-diagonal entries are already zero has `v_{jc} = 0`, so it keeps
them zero. Induction over finite sets of columns, and within a column over finite
sets of rows, turns the matrix of `g` into a diagonal matrix
`diag(c_1, …, c_d)` in `H` with the same value of `χ` and the same
determinant.

**Diagonal matrices.** Each single-coordinate scale
`diag(1, …, c_i, …, 1)` lies in `H`. For a splitting basis the
membership criterion `elementaryEnd_mem_iff` for a diagonal elementary
endomorphism does not depend on the coordinate. So the scale by `c_i` in
one fixed coordinate `j` also lies in `H`. Conjugation by the permutation
matrix of the transposition of `i` and `j` shows that `χ` takes the same
value on the two scales. The scales by `c_1, …, c_d` in coordinate `j`
multiply to the scale by `c_1 ⋯ c_d`, which is the determinant. So if `g`
has determinant one, then `χ(g) = χ(diag(c_1, …, c_d)) = 1`.

**Factorization.** The kernel of the determinant on `U^k(L)` therefore
lies in the kernel of `χ`. The homomorphism `η` on the determinant image
is the map that `χ` induces on the quotient by the determinant kernel,
composed with the inverse of `QuotientGroup.quotientKerEquivRange`.

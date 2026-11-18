# The regular matrix realization of a relative Brauer class

Let `L/K` be finite Galois and put `G = Gal(L/K)`. For a multiplicative
unit-valued two-cocycle `c`, `regularLift c s` is the invertible matrix indexed
by `G` that sends the basis vector at `t` to `c(s,t)` times the basis vector at
`st`. Lean constructs it by multiplying the left translation permutation matrix
by the diagonal matrix with entries `c(s,t)`. The matrix product for
`P_s s(P_t)` has at most one contributing term in each entry. The cocycle
identity gives the precise factorization `P_s s(P_t) = c(s,t) P_(st)`, with
`c(s,t)` embedded as a scalar matrix. The identity holds for arbitrary cocycles, including
unnormalized ones.

`regularAction` acts on a matrix `X` by `P_s s(X) P_s⁻¹`. The scalar in the
factorization disappears upon conjugation, so this defines a semilinear Galois
action. Its fixed algebra is `regularCSA c hc`. The existing finite Galois
descent construction proves that this actual algebra is finite-dimensional,
central and simple and supplies `regularSplittingChart`. The chart recovers the
regular action because it sends `l ⊗ a` to `l a` with `a` fixed. The construction
works in every characteristic, with `K`, `L` and the CSA in the same arbitrary
universe.

The weighted regular matrices and their factor-set identity implement the
surjectivity construction in J.-P. Serre, *Local Fields* (1979), Chapter X,
§5, proof of Lemma 1, printed pp. 158–159. The fixed algebra uses the Galois
descent for algebras of Chapter X, §2, Proposition 4, through the Library's
`SemilinearGaloisAction` interface.

# Coefficient matrices of the highest-weight subquotient

This module links the subquotient `X/Y` of Tits's Proposition 3.4 (module
`HighestWeightSubquotientRepresentation`) to the compressions of descended
algebras (module `Algebra/GaloisTwistedCompression`). It is the
representation-theoretic half of the simple-weight comparison (Tits,
*Représentations linéaires irréductibles d'un groupe réductif sur un corps
quelconque*, J. reine angew. Math. 247 (1971), Proposition 3.4, pp. 204–205). Its
conclusion: once a rational idempotent adapted to `X ⊇ Y` is chosen, the Tits
algebra of `X/Y` is a corner of the descended algebra of the ambient
representation.

Setting: `G` is affine over `k`, `ρ` is a representation of `G_K` on `Kⁿ`, `p` is a
split pinning of `G_K`, and `D : p.HighestSubquotientData ρ ν`.

## Declarations

- `MatrixRepresentation.coefficientMatrix_mulVec_mem`: the coefficient matrices
  `(id ⊗ φ)(universalMatrix ρ)` preserve every stable subspace. This is the
  definition of stability at the universal scalar test with the functional
  `id ⊗ φ`, rewritten by `functional_mulVec_algebraMap`.
- `HighestSubquotientData.proj_retr_mulVec_eq_zero`: `proj ∘ retr` kills `Y`.
  `HighestSubquotientData.retr_mulVec_of_mem`: `incl ∘ retr` is the identity on `X`.
- `HighestSubquotientData.compression`: let `f` be an idempotent matrix with
  `im f ⊆ X`, `f(Y) = 0` and `f x − x ∈ Y` for `x ∈ X`. Put `F = proj · retr · f`
  and `E = f · incl · sect`. Then `F E = 1`, `E F = f`, and every coefficient
  matrix of the subquotient is the compression `F X_φ(ρ) E`. The proofs are
  vector computations. `proj ∘ retr ∘ f` agrees with `proj ∘ retr` on `X`,
  coefficient matrices preserve `X` and `Y`, and the published intertwining
  identities give `incl X_φ(sub) = X_φ(ρ) incl` and
  `proj X_φ(sub) = X_φ(quot) proj` (`coefficientMatrix_intertwines_of`).
- `HighestSubquotientData.titsAlgebra_quot_eq_compressed`: if moreover
  - `f` lies in a twisted-fixed `k`-form `B ≤ twistedFixed P` containing the
    Tits algebra of `ρ`,
  - the subquotient is irreducible with scalar self-intertwiners and
    invertible intertwiners to its Galois twists, and
  - `K/k` is Galois,

  then the Tits algebra of the subquotient equals `compressed B F E` (by
  `titsAlgebra_eq_compressed`).

- `TitsSubquotientCompressionStatement` packages `compression` as a proposition. It
  quantifies over all fields `k ⊆ K`, affine `G`, split pinnings of `G_K`,
  representations on `Kᴺ`, weights `ν`, subquotient data and adapted idempotents.
  It is proved by `titsSubquotientCompression`.

No assumption on the characteristic is made.

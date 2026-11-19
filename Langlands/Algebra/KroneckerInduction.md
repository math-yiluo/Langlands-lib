# Kronecker products of matrix families and Galois induction of twisting matrices

This internal module provides the matrix algebra behind this development's
proof of the corestriction (transfer) law for the Tits obstruction (Tits,
*Représentations linéaires irréductibles d'un groupe réductif sur un corps
quelconque*, J. reine angew. Math. 247 (1971), Proposition 5.1, printed
p. 207 / PDF p. 12). Tits proves that proposition cohomologically, citing
reference [14] of his bibliography (printed p. 219 / PDF p. 24), S. Lang,
*Rapport sur la cohomologie des groupes* (1966), Proposition 13, p. 57. The matrix formulation
here, which induces twisting matrices from `Gal(K/E)` to `Gal(K/k)`, is this
development's own. It is the matrix counterpart of inducing a cocycle along
`Gal(K/E) ⊆ Gal(K/k)`.

Everything is in the namespace `Langlands.Algebra.KroneckerInduction`.

## Kronecker products of families (section `Kronecker`)

Let `R` be a commutative ring, `D` a finite index type and `n` a finite type.

- `piKronecker Z`: for `Z : D → Matrix n n R`, the matrix indexed by `D → n`
  whose `(a, b)` entry is `∏ σ, Z σ (a σ) (b σ)` (`piKronecker_apply`).
- `piKronecker_mul`, `piKronecker_one`: the Kronecker product of factorwise
  products is the product of the Kronecker products, and the Kronecker product
  of identity matrices is the identity. The product formula expands
  `∏ σ ∑ c, …` as a sum over functions `c : D → n` (`Finset.prod_univ_sum`).
- `piKronecker_map`: a ring homomorphism applied entrywise commutes with
  `piKronecker` (`map_prod`).
- `piKronecker_smul`: scalars of the factors multiply.
- `indexEquiv π : (D → n) ≃ (D → n)`, `a ↦ a ∘ π`, for a permutation `π` of
  `D` (`indexEquiv_apply`, `indexEquiv_symm_apply`).
- `piKronecker_perm`: permuting the factors along `π` reindexes rows and
  columns along `indexEquiv π`.
- `piKronecker_update`: the entry of a Kronecker product in which one factor
  is replaced, as that factor's entry times the product of the others.
- `piKroneckerMultilinear S`: `piKronecker` as an `S`-multilinear map, for any
  commutative semiring `S` with `Algebra S R` (`piKroneckerMultilinear_apply`).
  Additivity and homogeneity in each factor follow from `piKronecker_update`.
- `piKronecker_intertwine`: let `π` be a permutation of `D`, and let
  `F σ * Y σ = X (π⁻¹ σ) * F σ` for all `σ`. Then the Kronecker product of the
  `F σ`, with rows reindexed along `(indexEquiv π)⁻¹`, intertwines
  `piKronecker Y` with `piKronecker X`. Proof: apply `piKronecker` to the
  factorwise identities, use `piKronecker_mul` and `piKronecker_perm`, then
  reindex the rows of both sides.
- `isUnit_piKronecker`: a Kronecker product of invertible matrices is
  invertible, since the inverses' Kronecker product is a right inverse.
- `isUnit_submatrix_left`: reindexing only the rows of an invertible matrix
  along an equivalence keeps it invertible.

### Relation with `PiMatrixKronecker`

The published module `Langlands/Algebra/BrauerCorestriction/PiMatrixKronecker`
defines `Langlands.BrauerCorestriction.kroneckerMultilinear F E m`, the same
Kronecker product, for `m × m` matrices indexed by `Fin m` over a field `F`.
`piKronecker` allows an arbitrary finite index type `n` and an arbitrary
commutative coefficient ring `R`. Both are used later: the coefficient ring
of a universal matrix of a representation is not a field, and the twisted-fixed
algebras of `Algebra/GaloisTwistedMatrix` are indexed by arbitrary types. The
two constructions agree definitionally on their common domain; this is
`kroneckerMultilinear_eq_piKronecker` in `Algebra/CorestrictionTwistedFixed`.
This module does not import that one, so it can stay independent of the
Brauer group API.

## Galois induction (section `Induction`)

Let `k ⊆ E ⊆ K` be fields with `IsScalarTower k E K`.

- `InductionData k E K D`: data for inducing twisting matrices from
  `Gal(K/E) = K ≃ₐ[E] K` to `Gal(K/k) = K ≃ₐ[k] K`:
  - `ext : D → (K ≃ₐ[k] K)`, a lift of each index;
  - `perm : (K ≃ₐ[k] K) → Equiv.Perm D`, the permutation of indices induced
    by each `τ`;
  - `stab : (K ≃ₐ[k] K) → D → (K ≃ₐ[E] K)`, the correction terms;
  - `mul_ext`: `τ * ext σ = ext (perm τ σ) * stab τ σ` (with `stab τ σ`
    regarded as a `k`-automorphism).

  In the application `D` indexes the `k`-embeddings of `E` into a normal
  extension, `ext σ` extends the embedding `σ` to `K`, and `perm τ` is
  composition with `τ`. These relations hold for any choice of extensions
  `ext`; no group structure on `D` is used.
- `inducedFactor I Q τ σ'`: for twisting matrices `Q : (K ≃ₐ[E] K) → M_n(K)`,
  the matrix `ext σ' (Q (stab τ (perm τ⁻¹ σ')))`, entrywise.
- `inducedMatrix I Q τ`: the Kronecker product of the factors
  `inducedFactor I Q τ σ'`, with rows reindexed along
  `(indexEquiv (perm τ))⁻¹`. This is a matrix indexed by `D → n`.
- `isUnit_inducedMatrix`: if every `Q h` is invertible, so is every induced
  matrix. Entrywise application of the automorphism `ext σ'` preserves
  invertibility, because it commutes with the determinant (`RingHom.map_det`).
- `inducedMatrix_mul_piKronecker` (**Galois induction**): let `Gal(K/k)` act
  on a commutative `K`-algebra `R` by ring maps `act`, multiplicatively
  (`act (g g') = act g ∘ act g'`) and compatibly with `K`. Suppose the
  matrices `Z σ` over `R` satisfy the twisting equation
  `Q h · Z σ = act h (Z σ) · Q h` for all `h ∈ Gal(K/E)` (with `Q h` mapped
  into `R`). Then, for every `τ ∈ Gal(K/k)`,

  `C τ · ⨂_{σ'} ext σ' (Z (perm τ⁻¹ σ')) = act τ (⨂_σ ext σ (Z σ)) · C τ`,

  where `C τ = inducedMatrix I Q τ` and `ext σ` acts through `act`. Proof:
  1. Apply `act (ext σ')` to the twisting equation for
     `σ = perm τ⁻¹ σ'` and `h = stab τ σ`. By `mul_ext`,
     `ext σ' ∘ stab τ σ = τ ∘ ext σ`, so this gives the factorwise identity
     `F σ' · ext σ' (Z σ) = act τ (ext σ (Z σ)) · F σ'` with
     `F σ' = inducedFactor I Q τ σ'`.
  2. Take Kronecker products of both sides (`piKronecker_mul`,
     `piKronecker_map`). Rewrite the right-hand factor family as a permuted
     family (`piKronecker_perm`), then reindex the rows as in
     `piKronecker_intertwine`.

  This form, with a commutative coefficient ring `R`, is intended for the
  group side of the transfer law. There `R` is the coordinate ring of the
  group over `K` and the `Z σ` are universal matrices of representations, so
  the identity says that `C τ` intertwines a Kronecker product of
  representations with its Galois twist. The algebra side
  (`Algebra/CorestrictionTwistedFixed`) uses the same factors, through
  `inducedMatrix` and `piKronecker_intertwine`, for matrices over `K`.

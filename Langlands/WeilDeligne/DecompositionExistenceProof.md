# Existence of block decompositions with semisimple Weil part

`Langlands.WeilDeligneRepresentation.Blocks.decompositionExistence` proves the
published proposition
`Langlands.WeilDeligneRepresentation.Blocks.DecompositionExistence.{uG, uV}`
from `Langlands/WeilDeligne/BlockStatements.lean`, for arbitrary universes
`uG uV`:

```lean
theorem decompositionExistence : DecompositionExistence.{uG, uV}
```

Let `G` be any group and `ν : G →* ℂˣ` any character. Let
`A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν` be a pair whose Weil
representation is semisimple (`A.toFiniteRepresentation.IsSemisimple`). The
theorem produces `k : ℕ` and block data `d : Fin k → BlockDatum.{0, uG, uV} ℂ G`
with irreducible Weil factors, together with an isomorphism of pairs from `A` to
`directSum fun i => (d i).pair ν`. No hypothesis on `G` or `ν` is added. Each
Weil factor is a subrepresentation of the carrier of `A`, so it lives in the
carrier universe `uV`. The zero pair gives `k = 0`.

Throughout, `r = A.representation` and `N = A.monodromy`. All helpers are in
the namespace `Langlands.WeilDeligneRepresentation.Blocks.DecompositionExistenceProof`.
The proof works inside the carrier of `A` and never forms sub-pairs as separate
objects.

## Linear algebra of the monodromy

- `representation_monodromy_pow` turns covariance into
  `r(g) (N^j v) = ν(g)^j • N^j (r(g) v)`. It is proved by induction on `j`
  from `A.covariance`.
- `monodromy_pow_mem`: powers of `N` preserve an `N`-stable subspace.
- `kerPow A n` is `ker N^n` and `imagePow A σ n` is `N^n σ`, both as Weil
  subrepresentations. Stability follows from the covariance formula, because
  `ν(g)^n` is a unit.
- `wellFoundedLT_subrepresentation`: the lattice of subrepresentations embeds
  in the lattice of subspaces of the finite-dimensional carrier, so it is well
  founded. Hence it is atomic, and `eq_bot_or_exists_atom_le` applies.
- `isCompl_toSubmodule`: complementary subrepresentations have complementary
  underlying subspaces.

Semisimplicity is used as given by the statement: `IsSemisimple` is the
complemented-lattice property of subrepresentations, so `exists_isCompl`
supplies Weil-stable complements.

## The embedded block

For a subrepresentation `σ` and `m : ℕ`:

- `sumMap σ m : (Fin m → σ) →ₗ A` is `f ↦ Σ_j N^j (f j)`.
- `blockLinear σ m` is `sumMap σ m` composed with Mathlib's
  `TensorProduct.piScalarRight`, which identifies `σ ⊗ (Fin m → ℂ)` with
  `Fin m → σ`. On pure tensors, `blockLinear_tmul` gives
  `v ⊗ w ↦ Σ_j w_j • N^j v`, that is, `v ⊗ e_j ↦ N^j v`.
- `blockLinear_injective` and `range_blockLinear`: since `piScalarRight` is a
  linear equivalence, `blockLinear σ m` is injective when `sumMap σ m` is, and
  both maps have the same range.
- `pieceHom σ m hnil` packages `blockLinear σ m` as a morphism of pairs
  `Hom (block ν (FiniteRepresentation.of σ.toRepresentation) m) A`. The
  hypothesis `hnil` says that `N^m` kills `σ`. Both laws are checked on pure
  tensors with `TensorProduct.ext'`.
  - For the Weil action, the block acts by `r(g)` on `σ` and multiplies the
    `j`-th coordinate by `ν(g)^j` (`Special.action_apply`). The covariance
    formula matches this term by term.
  - For the monodromy, `block_monodromy_tmul` turns the block monodromy into
    `v ⊗ raising w`. After splitting off the first coordinate
    (`Fin.sum_univ_succ`) and the last one (`Fin.sum_univ_castSucc`), the
    raised sum equals `N (Σ_j w_j • N^j v)`. Indeed `raising w 0 = 0`,
    `raising w (i+1) = w i`, and the last term `N^m v` vanishes by `hnil`.

## The key injectivity lemma

`eq_zero_of_forall_monodromy_pow_mem` has the following hypotheses:
- `N^(n+1)` kills `σ`;
- `N^n` is injective on `σ`;
- `T` is a subspace meeting `N^n σ` trivially;
- `f : Fin (n+1) → σ` is such that every power `N^e` sends `Σ_j N^j (f j)` into `T`.

Under these hypotheses `f = 0`. Suppose not. Let `j0` be the least index with
`f j0 ≠ 0` (`Finset.min'`). Applying `N^(n-j0)` leaves only the term
`N^n (f j0)`: smaller indices have `f j = 0`, and larger ones are killed by
`N^(n+1)`. So `N^n (f j0)` lies in `T ∩ N^n σ = 0`, hence `f j0 = 0` by
injectivity, a contradiction. Taking `Σ_j N^j (f j) = 0`, so that every
`N^e` of it lies in `T`, gives `sumMap_injective`.

## One splitting step

`Piece A` records one embedded block. Its fields are:
- a subrepresentation `carrier`;
- a positive `length`;
- irreducibility of `carrier.toRepresentation`;
- a morphism of pairs `map` from `block ν (FiniteRepresentation.of carrier.toRepresentation) length` to `A`;
- injectivity of `map`.

`Piece.range` is the image of `map`.

`exists_piece` takes a nonzero `N`-stable subrepresentation `U`. It returns a
piece `p` and an `N`-stable subrepresentation `D` with
`p.range ⊔ D = U`, `dim p.range + dim D = dim U` and `0 < dim p.range`. The
proof has four parts.

1. **Order of nilpotency.** `A.nilpotent` gives some power of `N` vanishing
   on `U`. Let `n + 1` be the least such power (`Nat.find`). It is positive
   because `U ≠ ⊥`, so some `v ∈ U` has `N^n v ≠ 0`.
2. **The Weil factor.** Take a Weil complement `C` of `U ⊓ ker N^n`. Writing
   `v = a + c` with `a ∈ U ⊓ ker N^n` and `c ∈ C` gives `c ∈ C ⊓ U` with
   `N^n c ≠ 0`. Hence `C ⊓ U ≠ ⊥` contains an atom `σ`. The atom is
   irreducible by the Library lemma
   `Langlands.FiniteIndexRestriction.isIrreducible_toRepresentation_of_isAtom`.
   Since `σ ⊆ U`, `N^(n+1)` kills `σ`. Since `σ ⊆ C`, `N^n` is injective on
   `σ`. The piece is `pieceHom σ (n+1)`, which is injective by
   `sumMap_injective`. Its range is `range (sumMap σ (n+1))`. Since `σ ≠ ⊥`,
   that range has dimension `(n+1) · dim σ > 0`, and it lies in `U` by
   `monodromy_pow_mem`.
3. **The complement.** Take a Weil complement `T` of `N^n σ`, and set
   `D = U ⊓ ⋂_e (N^e)⁻¹ T`.
   - `D` is Weil-stable: `N^e (r(g) x) = ν(g)^(-e) • r(g) (N^e x)`.
   - `D` is `N`-stable: `N^e (N x) = N^(e+1) x`.
   - `D` meets the range of the piece trivially, by the key lemma.

   This set corresponds to the statement Markdown's `{v : p(N^j v) = 0 for all j}`, for the projection
   `p` onto `N^n σ` with kernel `T`.
4. **Dimension count.** Consider `Ψ : A → (Fin (n+1) → A ⧸ T)`,
   `x ↦ (N^j x mod T)_j`. The image of its kernel on `U` lies in `D`: for
   `e ≥ n + 1` the power `N^e` already vanishes on `U`. Moreover
   `dim (A ⧸ T) = dim N^n σ = dim σ`, by complementarity and injectivity of
   `N^n` on `σ`. Rank–nullity then gives `dim D ≥ dim U - (n+1) · dim σ`.
   Together with disjointness (`Submodule.finrank_sup_add_finrank_inf_eq`),
   this forces `range ⊔ D = U` (`Submodule.eq_of_le_of_finrank_le`). It also
   gives the additive dimension formula.

## Induction and assembly

`exists_pieces` proceeds by strong induction on `dim U`, for every `N`-stable
subrepresentation `U`. It produces `k` and `p : Fin k → Piece A` with
`⨆ i, (p i).range = U` and `Σ_i dim (p i).range = dim U`. For `U = ⊥` take
`k = 0`. Otherwise apply `exists_piece`, then the induction hypothesis to `D`,
which has smaller dimension. Prepend the new piece with `Fin.cons`, using
`Fin.sum_univ_succ` for the dimensions.

`nonempty_equiv_directSum_of_span` is the assembly step. Suppose morphisms of
pairs `φ i : Hom (B i) A`, indexed by `Fin k`, have images spanning `A`, and
the dimensions of the `B i` add up to `dim A`. Then `A` is isomorphic to
`directSum B`. The map `Φ = DirectSum.toModule (fun i => φ i)` commutes with
the Weil actions and with the monodromies. Both laws are checked on each
summand (`DirectSum.linearMap_ext`, `DirectSum.lmap_lof`,
`DirectSum.toModule_lof`): the direct sum's action and monodromy are
componentwise `DirectSum.lmap`. `Φ` is surjective because its range contains
every image. By `Module.finrank_directSum` its source has the same dimension
as `A`, so `Φ` is bijective. `Representation.IntertwiningMap.ofBijective`
gives an equivalence of pairs from `directSum B` to `A`, whose inverse is
taken.

The main theorem applies `exists_pieces` to `U = ⊤`. Here
`d i = ⟨FiniteRepresentation.of (p i).carrier.toRepresentation, (p i).length, (p i).length_pos⟩`,
so that `(d i).pair ν` is by definition the source of `(p i).map`.
Irreducibility of `d i` is the field `(p i).isIrreducible`. The dimension
hypothesis of the assembly follows from `LinearMap.finrank_range_of_inj` for
each injective piece, together with `finrank_top`.

## Provenance

The argument follows the outline in the statement's Markdown
(`Langlands/WeilDeligne/BlockStatements.md`, section "Decomposition and
criteria over `ℂ`, with no hypothesis on the group"). That outline cites
Henniart 2002 §2.2–2.3 and Tate 1979, 4.1.4–4.1.5. The implementation
differs from the outline in three ways.

- The complement `C` is taken of `U ⊓ ker N^n` rather than `ker N^(m-1)`,
  and `σ` is an atom of `C ⊓ U`. This lets the step run inside an arbitrary
  stable subspace `U`.
- The projection is replaced by the Weil complement `T` of `N^n σ`.
- The final isomorphism is assembled from the internal spanning family
  instead of an internal direct-sum decomposition.

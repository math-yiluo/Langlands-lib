# Trigonalizable groups and stable flags (Milne 16.2, (a) ⇔ (b))

This helper module proves the first equivalence of
`Langlands.GroupScheme.TrigonalizableCharacterizationStatement` (see
[`CharacterizationStatement`](CharacterizationStatement.md)): an affine group
scheme `G` over a field `k` is trigonalizable exactly when every matrix
representation stabilizes a maximal flag. The declarations are in the
namespace `Langlands.GroupScheme.Trigonalizable`. Nothing new is defined.

Throughout, a maximal flag of `kⁿ` with `d = Fintype.card n` is encoded as in
the statement: a monotone family `W : Fin (d + 1) → Submodule k (n → k)` with
`Module.finrank k (W i) = i` and every `W i` a stable subspace
(`ρ.IsStableSubspace`).

## Declarations

- `finrank_comap_of_surjective`: for a surjective linear map `f : E → F`
  between vector spaces over a field, `E` finite-dimensional, and a subspace
  `U ⊆ F`, `finrank (U.comap f) = finrank U + finrank (ker f)`.
  *Proof.* Rank–nullity for the restriction of `f` to `U.comap f`, whose
  range is `U` (surjectivity) and whose kernel is `ker f`.

- `dimension_add_one_of_line`: for `v ≠ 0` and a quotient representation
  `q : QuotientRepresentation ρ (k ∙ v)` (Library structure in
  [`MatrixRepresentation.QuotientCoordinates`](../MatrixRepresentation/QuotientCoordinates.md):
  a representation on `k^{q.dimension}` with a surjective intertwining
  projection matrix whose kernel is `k ∙ v`), `q.dimension + 1 = card n`.
  *Proof.* Rank–nullity for the projection, using
  `QuotientRepresentation.projection_surjective`, `ker_projection` and
  `finrank_span_singleton`.

- `exists_stableFlag_of_card_eq` (Milne 16.2, (a) ⇒ (b), assuming
  `[IsAffineHom G.X.hom]` and `IsTrigonalizable G`): for every `d`, every
  representation `ρ` on `kⁿ` with `card n = d` has a stable maximal flag
  indexed by `Fin (d + 1)`.
  *Proof.* Induction on `d`, generalizing over `n` and `ρ`.
  For `d = 0` take the constant family `⊥` (`isStableSubspace_bot`).
  For `d + 1`, `n` is nonempty, so `IsTrigonalizable G` gives `v ≠ 0`
  spanning a stable line. By `IsStableLine.isStableSubspace` (module
  [`StableLines`](StableLines.md)), `k ∙ v` is a stable subspace, and the
  Library's `nonempty_quotientRepresentation` gives a quotient representation
  `q` by it, of dimension `d` by `dimension_add_one_of_line`. The induction
  hypothesis gives a stable maximal flag `W'` of `q.representation`. The new
  flag is `W = Fin.cons ⊥ (fun i => (W' i).comap q.projection)`, that is,
  `W 0 = 0` and `W (i+1)` is the preimage of `W' i`. Monotonicity follows
  from `Submodule.comap_mono`. The dimensions are `0` and
  `finrank (W' i) + 1 = i + 1`, by `finrank_comap_of_surjective`. Stability
  of each preimage is `IsStableSubspace.comap` applied with
  `q.intertwines`.

- `isTrigonalizable_of_exists_stableFlag` (Milne 16.2, (b) ⇒ (a), assuming
  `[IsAffineHom G.X.hom]`): if every representation has a stable maximal
  flag, then `G` is trigonalizable.
  *Proof.* For nonempty `n`, the term `W 1` has dimension `1`, so
  `finrank_eq_one_iff'` gives a nonzero `w` with `W 1 = k ∙ w`. Then `k ∙ w`
  is a stable subspace, and `isStableLine_of_isStableSubspace` (module
  `StableLines`) makes `w` span a stable line.

- `isTrigonalizable_iff_exists_stableFlag`: the equivalence (a) ⇔ (b) in
  exactly the form of the first conjunct of the target statement, assembled
  from the two previous theorems (with `d = card n`).

## Provenance

The equivalence is Milne, *Algebraic Groups* (2017), Proposition 16.2,
(a) ⇔ (b), pp.324–325 (source ID `milne-2017-algebraic-groups`). The Lean
proof of (a) ⇒ (b) follows Milne's induction on `dim V` with a stable line
`V_1` and a stable maximal flag of `V/V_1`. The proof of (b) ⇒ (a) reads off
the one-dimensional term of the flag. The two dimension lemmas are
elementary rank–nullity adapters.

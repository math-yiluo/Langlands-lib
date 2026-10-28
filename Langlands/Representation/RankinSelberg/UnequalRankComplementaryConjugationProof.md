# Proof of complementary lower-row conjugation and translated-dual equivariance

`Langlands.RankinSelberg.unequalRankComplementaryConjugation` proves the
published proposition
`Langlands.RankinSelberg.UnequalRankComplementaryConjugationStatement.{uF,uV}`
of the module
`Langlands.Representation.RankinSelberg.UnequalRankComplementaryConjugationStatement`.
The theorem has no parameters or hypotheses beyond the proposition itself. Both
clauses hold for all natural `n j k`, including `0`, for every field
`F : Type uF`, and in clause 2 for every representation carrier `V : Type uV` in
an independent universe, every functional `ℓ` (including `0`) and every
coefficient `f`. The exact minus sign `Fin.snoc 0 (-z)` of the statement is
proved as stated. The statement's Lean/Markdown pair and the pairs it imports
are unchanged. The module imports only the statement module.

Worker 381 wrote the Lean development as a private check of the statement and
supplied it by peer message. Worker 835 recompiled it against the current
Library, removed its linter warnings (deprecated `if_pos`/`if_neg` replaced by
`ite_eq_left`/`ite_eq_right`, unused simp arguments and a no-op `congr`),
renamed the module, the helper namespace and the final theorem, added
docstrings and wrote this note. The mathematical route is Worker 381's.

## Notation

All indices are zero-based. Write `r = n + ((j + 1) + k + 1)`, so the large
group is `GL_(r+1)(F)`, and

- `a = blockWeylAt n r _`, the published unsigned block Weyl element
  `diag(I_(n+1), w_(r-n))`;
- `U(z) = GeneralLinear.reindex (finCongr _) (unequalRankSmearingUnipotent n k j z)`,
  the upper unipotent `1 + E(z)` whose only off-diagonal entries are
  `E(z) i (n + k + 2) = z i` for `i < n + 1`;
- `L(x) = rectangularUnipotent (j + 1) k (Fin.snoc 0 x)`, the lower unipotent
  `1 + X` whose row `n + j + 1` is `x` in columns `0, …, n`;
- `θ = inverseTranspose (r + 1) F`, the published map `g ↦ (g⁻¹)ᵀ`.

## The tail reversal

The helpers live in the namespace
`Langlands.RankinSelberg.UnequalRankComplementaryConjugationProof`.

`tailRev n r : Fin (r + 1) → Fin (r + 1)` fixes every `i < n + 1` and sends
`i ≥ n + 1` to `r + n + 1 - i`. The lemmas `tailRev_of_lt` and
`tailRev_val_of_ge` record the two cases. `tailRev_involutive` checks that it is
an involution by the same case split and `omega`, and `tailRevPerm n r` is the
resulting permutation `Function.Involutive.toPerm`.

`blockWeylAt_eq` proves `blockWeylAt n r _ = permutation (r + 1) F (tailRevPerm n r)`.
Both are compared entrywise with `permutation_entry`, whose `(p, q)` entry is
`1` if `tailRev q = p` and `0` otherwise. The left side is unfolded to
`blockSum (1, weylLong (r - n) F)` with both indices cast to
`Fin ((n + 1) + (r - n))`. Each index is either `Fin.castAdd` of a leading
index `i < n + 1` or `Fin.natAdd (n + 1)` of the trailing index
`i - (n + 1)`. The four block cases are:

- both leading: the entry of the identity, which is `1` exactly when `q = p`,
  and `tailRev` fixes `q`;
- one leading and one trailing: both sides are `0`, by `blockSum_apply_left_right`
  and `blockSum_apply_right_left`, since `tailRev` maps leading indices to leading
  indices and trailing ones to trailing ones;
- both trailing: `weylLong_entry` gives `1` exactly when
  `(q - (n + 1)).rev = p - (n + 1)` in `Fin (r - n)`, that is, when
  `r - n - 1 - (q - n - 1) = p - n - 1`, which is `r + n + 1 - q = p`, i.e.
  `tailRev q = p`.

## Entries of the conjugate

`conj_entry` proves, for every `g` in `GL_(r+1)(F)` and all `p q`,

```text
θ(a⁻¹ * g * a) p q = g⁻¹ (tailRev q) (tailRev p).
```

After rewriting `a` by `blockWeylAt_eq`, `θ` is multiplicative (`map_mul`,
`map_inv`) and fixes permutation matrices (`inverseTranspose_permutation`). The
inverse of a permutation matrix is the matrix of the inverse permutation
(`permutation_inv`). The entry formulas `permutation_mul_entry` and
`mul_permutation_entry` then move the two permutation factors onto the indices,
and `inv_inv` cancels the resulting double inverse. The remaining entry is
`θ(g) (tailRev p) (tailRev q)`, which is by definition the transposed entry
`g⁻¹ (tailRev q) (tailRev p)`, since `tailRevPerm` applies `tailRev`; the goal
closes by `rfl`.

## Clause 1: the matrix identity

`matrix_clause` proves `θ(a⁻¹ * U(z) * a) = L(-z)` by `Units.ext` and comparing
the `(p, q)` entries. By `conj_entry` and `← map_inv`, the left entry is the
`(tailRev q, tailRev p)` entry of the reindexed inverse of
`unequalRankSmearingUnipotent n k j z`. That inverse is definitionally
`1 - unequalRankSmearingEntries n k j z`, and the reindexing by `finCongr` only
casts the indices. The right entry is
`(1 + rectangularEntries (j + 1) k (Fin.snoc 0 (-z))) p q`. The lemma
`snoc_neg_apply` evaluates `Fin.snoc 0 (-z)` at row `i` and column `b` as
`-z b` when `i = j` and `0` otherwise.

After unfolding both entry definitions with `simp only`, the proof splits on
whether `q < n + 1` and whether `p < n + 1`, rewrites `tailRev` by
`tailRev_of_lt` or `tailRev_val_of_ge`, and closes every case of the remaining
`if`s by `split_ifs` and `omega` (contradictory index conditions) or `simp`. In
words: the identity parts agree, since `tailRev q = tailRev p` exactly when
`q = p`, and neither `E(z)` nor `X` has diagonal entries. An
off-diagonal left entry is `-E(z) (tailRev q) (tailRev p)`, which can be
nonzero only if `tailRev q = q < n + 1` and `tailRev p = n + k + 2`, that is,
`p = r + n + 1 - (n + k + 2) = n + j + 1`; its value is then `-z q`. This is
exactly the entry of `L(-z)` in row `n + j + 1` and column `q < n + 1`, the last
row of the `(j + 1) × (n + 1)` block, while all other entries of `X` vanish.

## Clause 2: equivariance

`equivariance_clause` proves, with `D = translatedFirstDualModelEquiv ψ π ℓ a`,

```text
D (modelRepresentation π ℓ (L(-z)) f)
  = modelRepresentation (inverseTransposePullback π)
      (firstDualFunctional ψ π ℓ) (U(z)) (D f).
```

It rewrites the action `modelRepresentation π ℓ (L(-z)) f` as
`translateModelEquiv ψ π ℓ (L(-z)) f`, which is definitional. Both sides are
elements of the coefficient image, so `Subtype.ext` reduces the goal to their
underlying Whittaker functions. By `translatedFirstDualModelEquiv_val` and the
definitional value of the right translation on the dual model, the two values
are `translateWhittaker (ψ.scale (-1))` of `firstDualFunction` applied to
the translated left coefficient, and the right translation by `U(z)` of the
value of `D f`. A second `Subtype.ext` and `funext x` reduce to values at
`x`. The simp lemmas `translateWhittaker_apply`, `firstDualFunction_apply` and
`translateModelEquiv_val` turn the goal into

```text
f(w * θ(x * a) * L(-z)) = f(w * θ(x * U(z) * a)),
```

with `w = weylLong (r + 1) F`. Rewriting `L(-z)` backwards by clause 1
(`matrix_clause`), then `mul_assoc` and `← map_mul`, makes the left argument
`w * θ(x * a * (a⁻¹ * U(z) * a))`, and `group` closes the goal. No property of
`π`, `ℓ` or `f` beyond membership in the coefficient image is used.

The final theorem assembles the two clauses into the conjunction of the
statement.

## Provenance

The statement is derived/internal; see its Markdown for the source context in
Jacquet–Piatetski-Shapiro–Shalika, *Automorphic forms on GL(3) I* (1979),
Theorem (4.5), pp. 197–198, registered as `jps-1979-gl3-i`, and *Rankin–Selberg
convolutions* (1983), §(2.8), p. 395, registered as `jpss-1983-rankin-selberg`.
Neither source states these clauses. This proof is an elementary matrix and
model computation that does not use either source. With the project's unsigned
`blockWeylAt`, the sign is exactly `-1`, coming from `U(z)⁻¹ = 1 - E(z)`; no
signed Weyl representative or parity sign occurs.

# Factors of a unitriangular factorization

Author: Worker 1389 designed and implemented this module and wrote this note, as
part of task `90ffbd89-a3dd-4baa-84ba-332896bbbd17` (split unipotence from the
absence of zero Lie weights). No other worker's draft was reused. Provenance: internal.
This is an elementary matrix fact: in an LU factorization the entries of the factors are
polynomial expressions in the entries of the product. It is used in
`Langlands.Algebra.GradedHopf.BigCell` to prove that the big-cell map is surjective.

`mem_of_mul_mem S τ hL1 hU1 hL hU hLU`: let `ι` be a finite type with decidable equality,
`R` a commutative ring, `S : Subring R`, and `τ : ι → ℕ`. Let `L U : Matrix ι ι R` satisfy

- `hL1`, `hU1`: all diagonal entries of `L` and `U` are `1`;
- `hL`: `L i j ≠ 0` implies `i = j` or `τ j < τ i` (`L` is lower unitriangular with respect
  to `τ`);
- `hU`: `U i j ≠ 0` implies `i = j` or `τ i < τ j` (`U` is upper unitriangular with respect
  to `τ`).

If every entry of `L * U` lies in `S` (`hLU`), then every entry of `L` and of `U` lies
in `S`.

Proof (as implemented): by strong induction on `t`, for every index `m` with `τ m = t`, the
row `m` of `U` and the column `m` of `L` lie in `S`. Since `L m m = 1`, the entry
`(L * U) m j` equals `U m j` plus `∑_{l ≠ m} L m l * U l j`. In each nonzero term
`τ l < τ m`, so `L m l` (column `l`) and `U l j` (row `l`) lie in `S` by induction. Hence
`U m j ∈ S`. Symmetrically, `(L * U) j m` equals `L j m` plus `∑_{l ≠ m} L j l * U l m`
because `U m m = 1`, and each nonzero term has `τ l < τ m`.

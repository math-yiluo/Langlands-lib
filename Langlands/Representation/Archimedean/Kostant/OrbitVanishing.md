# Proof of the orbit statement

This module proves `orbitVanishing : OrbitVanishingStatement n`, the statement from
`Kostant/Coadjoint`. Here `ι` is a finite index type, `n : ι → ℕ` gives the block sizes, and
the field is `ℂ`. Let `W` be a space of polynomials in the coordinates `X ⟨i, p, q⟩`. Assume it
is stable under the coadjoint derivations `coadDer (E i a b)` for `a ≠ b`. Assume also that
every element of `W` vanishes at the regular nilpotent tuple `ψ` whose block `i` has entry
`c i p ≠ 0` at position `(p, p+1)` and `0` elsewhere. Then every element of `W` vanishes at
every tuple of nilpotent matrices.

This is the orbit step of the proof of Kostant's theorem along Matumoto's route (Matumoto
1987). The symbols of the annihilator vanish at `ψ`, and their zero set is stable under the
group, so they vanish on the closure of the regular nilpotent orbit. By a classical fact due to
Kostant, this closure is the whole nilpotent cone. The Lean proof does the closure step
concretely. It does not use the Zariski closure of the orbit: it uses triangularization and a
density argument on strictly upper triangular matrices.

## Notation

* `tuplePoint n Y` is the point `v ↦ Y v.1 v.2.1 v.2.2` of `Coord n → ℂ` given by a tuple of
  matrices `Y`.
* `zeroSet n W` is the set of tuples `Y` at which every element of `W` vanishes.
* `PreservesZeroSet n W i g` says that replacing block `i` of any `Y ∈ zeroSet n W` by
  `g * Y i * g⁻¹` stays in `zeroSet n W`.
* `regularTuple n c` is the tuple `ψ` above.

## Steps

1. **Coadjoint derivations on variables.** `coadDer_X_mk` writes out `coadDer x (X ⟨j, r, q⟩)`.
   `coadDer_unit_X_same` and `coadDer_unit_X_of_ne` specialise it to `x = E i a b`.

2. **Flow.** For `a ≠ b`, `transvection_conj_apply` computes the entries of
   `(1 + s E_ba) Y (1 - s E_ba)`. `flowEval n Y i a b` evaluates a polynomial along this flow,
   with block `i` conjugated over `ℂ[s]`, so it gives a polynomial in `s`.
   `eval_flowEval` says that its value at `s` is the evaluation at the conjugated tuple.
   `derivative_flowEval` says that its `s`-derivative is the flow of `coadDer (E i a b) f`.
   This is checked on variables, using the Leibniz rule and induction on `f`.

3. **Transvection invariance.** `update_transvection_mem_zeroSet` takes `f ∈ W` and
   `Y ∈ zeroSet n W`. All iterated derivations of `f` lie in `W`, so every `s`-derivative of
   the flow polynomial vanishes at `s = 0` (`Polynomial.coeff_iterate_derivative`). Hence the
   flow polynomial is zero, and `f` vanishes along the whole flow.
   `preservesZeroSet_transvection` restates this as: every transvection `1 + c E_kl`, `k ≠ l`,
   preserves the zero set.

4. **Closure properties.** Preservation is closed under products (`PreservesZeroSet.mul`),
   holds for `1` (`preservesZeroSet_one`), and is closed under nonzero scalar multiples of
   invertible matrices (`PreservesZeroSet.smul`), since scalars cancel in `g Y g⁻¹`.

5. **Diagonal matrices of determinant one.** `diagonal_eq_transvection_mul` is an identity
   checked entrywise: in the `k, l` plane,
   `diag(t, t⁻¹) = (1 + (t-1)E_kl)(1 + E_lk)(1 + (t⁻¹-1)E_kl)(1 - tE_lk)`. With step 3 it gives
   `preservesZeroSet_diagonal_pair`. `preservesZeroSet_diagonal_of_prod_eq_one` treats a
   diagonal `D` with `∏ D r = 1` by fixing an index `l0` and using induction over finite sets
   `s` not containing `l0`. At each step it multiplies by one pair matrix `diag(D k, (D k)⁻¹)`
   on the `k, l0` plane.

6. **All invertible matrices.** `preservesZeroSet_of_det_eq_one` applies Mathlib's
   `Matrix.diagonal_transvection_induction`: a matrix is a product of transvections and a
   diagonal matrix of the same determinant. For `preservesZeroSet_of_isUnit`, the block size 0
   is trivial. Otherwise choose `μ` with `μ ^ (n i) = det g` (`ℂ` is algebraically closed).
   Then `μ⁻¹ • g` has determinant one, and step 4 removes the scalar. `conj_mem_zeroSet`
   conjugates all blocks at once, using induction over finite sets of block indices.

7. **Regular strictly upper triangular tuples.** Let `U` be strictly upper triangular with
   nonzero superdiagonal in each block. By `exists_conj_of_regular` from
   `Kostant/NilpotentConjugacy`, each block `U i` is conjugate to `ψ i`. So `U ∈ zeroSet n W`
   by step 6, since `ψ ∈ zeroSet n W` by hypothesis.

8. **Density.** Let `U` be any strictly upper triangular tuple and `g ∈ W`. Let `F` be `g`
   with every variable `X ⟨i, p, q⟩` with `p ≥ q` replaced by `0` (`bind₁`). Evaluating `F`
   at `x` is evaluating `g` at the strictly upper triangular truncation of `x`. Take the box
   with side `ℂ \ {0}` in the superdiagonal coordinates and `ℂ` in the other coordinates.
   On this box the truncation is regular, so `F` vanishes there by step 7. Every side is
   infinite, so `F = 0` (`MvPolynomial.funext_set`). Hence `g` vanishes at `U`, which equals
   its own truncation.

9. **Nilpotent tuples.** By `exists_conj_strictUpper` from `Kostant/NilpotentConjugacy`, each
   nilpotent block `M i` has an invertible `g i` with `g i * M i * (g i)⁻¹` strictly upper
   triangular. This tuple lies in the zero set by step 8. Conjugating back by `(g i)⁻¹` (step 6)
   puts `M` in the zero set, which is the claim of `OrbitVanishingStatement`.

## Imports

`Kostant/Coadjoint` (the statement and `coadDer`) and `Kostant/NilpotentConjugacy` (both
matrix facts above). From Mathlib: `MvPolynomial.funext_set`, `bind₁`,
`Matrix.diagonal_transvection_induction`, and the algebraic closedness of `ℂ`.

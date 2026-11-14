# A finite-dimensional cyclicity lemma for the cell matrix

Author: Worker 392.

This helper module of the proof of
`Langlands.Conductor.OrderedUnramifiedSphericalCyclicityStatement` (see
[`OrderedUnramifiedSphericalCyclicity`](../OrderedUnramifiedSphericalCyclicity.md))
is pure linear algebra over `ℂ`. All declarations are in
`Langlands.Conductor.SphericalCyclicity`. It imports only Mathlib.

## The matrix

`cellMatrix r q z : Matrix (Fin r) (Fin r) ℂ`, for `r q : ℕ` and `z : Fin r → ℂ`, is

```
M j i = (z j * q^(j+1))⁻¹ * (q^(j+1)             if j = i,
                             (q - 1) * q^i        if j < i,
                             0                    if j > i).
```

It is an internal auxiliary definition, with no literature source. It is the
matrix by which the parahoric Hecke operator of [`Hecke`](Hecke.md) acts on the
values of a parahoric-invariant vector at the Weyl representatives `w_0, …, w_(r-1)`,
up to the nonzero scalar `heckeConst`.

## The lemma

`eq_top_of_cellMatrix_stable`: let `2 ≤ q`, let every `z i` be nonzero and let
`i ↦ ‖z i‖` be monotone. Let `W` be a complex subspace of `Fin r → ℂ` that contains
the all-ones vector and satisfies `M v ∈ W` for every `v ∈ W`. Then `W = ⊤`.

The private helper `sum_filter_lt_succ` splits the sum over `{j | j < k + 1}` into
the sum over `{j | j < k}` plus the term at `k`.

## Proof

The proof is by contradiction, assuming `W ≠ ⊤`.

1. **An eigenfunctional.** The dual annihilator `W⁰` is nonzero, because
   `Submodule.dualAnnihilator_eq_bot_iff` holds and `W ≠ ⊤`. Let `A` be the
   multiplication-by-`M` endomorphism. Its transpose maps `W⁰` into itself, since
   `W` is `M`-stable. `Module.End.exists_eigenvalue` over the algebraically closed
   field `ℂ` gives a nonzero `φ ∈ W⁰` and `μ : ℂ` with `φ (A v) = μ φ v` for all `v`.
2. **Coordinates.** Write `L i = φ (e_i)`, so that `φ v = Σ_i v_i L_i`. Write
   `ν j = L j / (z j q^(j+1))` and `P k = Σ_{j < k} ν j`. Apply the eigen-equation to
   `e_i`. Because `M` is upper triangular, this gives
   `q^(i+1) ν_i + (q - 1) q^i P_i = μ L_i`.
3. **Telescoping.** Induction on `k` gives `q^k P_k = μ Σ_{j<k} L_j` for `k ≤ r`.
   The all-ones vector lies in `W`, so `Σ L_j = 0`. At `k = r` this gives
   `Σ_j ν_j = 0`.
4. **The ends of the support.** The functional is nonzero, so some `L i ≠ 0`. Let
   `i0` and `k1` be the least and the greatest index with `L i ≠ 0`.
   - At `i0` we have `P i0 = 0`, and the equation of step 2 gives `μ z_(i0) = 1`.
   - At `k1` we have `Σ ν = 0`, so `P k1 = -ν k1`. The equation of step 2 then
     gives `μ q z_(k1) = 1`.
5. **Norms.** We have `μ ≠ 0`, so `z i0 = q z k1` and `‖z i0‖ = q ‖z k1‖`.
   Monotonicity and `i0 ≤ k1` give `‖z i0‖ ≤ ‖z k1‖`. With `‖z k1‖ > 0` and
   `q ≥ 2`, this is a contradiction (`nlinarith`).

Only monotonicity of the norms is used, not strict monotonicity. Equal norms and
repeated parameters are allowed.

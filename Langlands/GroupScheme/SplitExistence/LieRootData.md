# Root operators with integral Lie brackets (`LieRootData`)

Author: Worker 1398.

Module `Langlands.GroupScheme.SplitExistence.LieRootData`. It is the first module of the
derivation of the group commutator relations from the Lie relations (step P3 of the split
existence proof, task 2132924b).

## Declarations

- `LieRootData P`: a structure for a root datum `P : RootDatum J X Y`. Its fields are the root
  operator fields of `ChevalleyData` (`n`, `wt`, `e`, `e_zero`, `e_mul`, `e_eq_zero`,
  `e_weight`, `e_one_map_ne_zero`), together with the integral bracket relation `lie_e_e`: for
  roots `j, j'` with `root j' ≠ -root j`, the commutator `[e j 1, e j' 1]` is `0` or `c • e k 1`
  for an integer `c` and a root `k` with `root k = root j + root j'`.
- `isDividedPowerFamily`: each `e j` is a divided-power family (module `RootExp`).
- `em R j i = e_j^{(i)}` and `E R j = em R j 1` as matrices over a commutative ring `R`. Their
  basic identities: `em_zero`, `em_eq_zero` (for `i > n`), `em_mul_em` (binomial
  multiplication), `E_mul_em` and `em_mul_E` (`E_j e_j^{(i)} = (i + 1) e_j^{(i+1)}`), `divExp_eq`,
  `commute_E_em` and `commute_E_divExp`.
- `sigma R j m B = σ_m(B) = Σ_{i + i' = m} (-1)^{i'} e_j^{(i)} B e_j^{(i')}`, with
  `sigma_zero` (`σ_0(B) = B`) and the recursion `sigma_succ`:
  `(m + 1) σ_{m+1}(B) = E_j σ_m(B) - σ_m(B) E_j`.
- `conj_eq_sum`: over every commutative ring,
  `x_j(g) B x_j(-g) = Σ_{m ≤ 2n} g^m σ_m(B)`, where `x_j(g) = divExp (e j) g`.

Proofs: `sigma_succ` expands both sides over antidiagonals and uses `E_mul_em` and `em_mul_E`.
`conj_eq_sum` multiplies out the two truncated exponentials and regroups the terms by total
degree.

Provenance: internal. This is the divided-power form of the expansion
`Ad(exp(g E)) = exp(g ad E)` used for Chevalley groups (Steinberg, *Lectures on Chevalley
groups*, §§2–3).

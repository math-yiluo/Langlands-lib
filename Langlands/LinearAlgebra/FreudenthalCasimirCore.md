# Freudenthal's recursion from the Casimir element

Module `Langlands.LinearAlgebra.FreudenthalCasimirCore`. The main theorem is
`Langlands.LinearAlgebra.freudenthalCasimirCoreStatement`, and the auxiliary
results are in namespace `Langlands.LinearAlgebra.FreudenthalCasimir`.

## Main theorem

`freudenthalCasimirCoreStatement : FreudenthalCasimirCoreStatement` proves the
proposition of `Langlands.LinearAlgebra.FreudenthalCasimirCoreStatement`
without further hypotheses. The proof is the trace computation of Humphreys,
*Introduction to Lie Algebras and Representation Theory*, GTM 9, §22.3. The
Casimir element is built in `Langlands.LinearAlgebra.FreudenthalCasimirAlgebra`
from the trace form of `U`, and its trace on each `V ⊓ W μ` is computed in two
ways. Notation: `F = GramDual.form P yb (mult W)`, `α_i = root i`,
`n(μ) = dim (V ⊓ W μ)`, and `e_i`, `f_i`, `t_j`, `t^j` and the Casimir element
`Ω = ∑_j t_j t^j + ∑_i e_i f_i` are as in `FreudenthalCasimirAlgebra`.

## Traces on invariant subspaces (section `TraceOn`)

`trOn V z` is the trace of `z` restricted to `V` when `z` maps `V` into
itself, and `0` otherwise. Its properties:

- `trOn_eq`: the restricted trace, when `z` preserves `V`;
- `trOn_add`, `trOn_zero`, `trOn_sum`: additivity for endomorphisms
  preserving `V`;
- `trOn_eq_mul_finrank`: if `z v = c v` for all `v ∈ V`, then
  `trOn V z = c · dim V`;
- `trOn_eq_zero_of_eq_bot`: the trace on the zero subspace is `0`;
- `trOn_mul_comm`: if `e` maps `A` into `B` and `f` maps `B` into `A`, then
  `trOn A (f e) = trOn B (e f)`. This is `LinearMap.trace_comp_comm'` for the
  restrictions.

## The computation (section `Core`)

The ambient hypotheses are those of `FreudenthalCasimirCoreStatement`:
`h : Hyp P W g root` (hypotheses 1–12) and `hV`, `g`-stability of `V`
(hypothesis 13). The later results also use `hirr`, `hlam`, `hpos`, `hneg`
(hypotheses 14–17).

- `mem_inf_of_mem`: an element of `g` of degree `χ` maps `V ⊓ W μ` into
  `V ⊓ W (μ + χ)`.
- `commutator_e_f_apply`: `e_i f_i - f_i e_i` acts on `W μ` by `F(μ, α_i)`.

  Proof. The commutator lies in `g` and has degree `0`, so it equals `τ a`
  (`Hyp.exists_eq_τ`). For each `l`,
  `trace (t_l (e_i f_i - f_i e_i)) = trace ((t_l e_i - e_i t_l) f_i)`, since
  the other term is a difference of traces of the products `e_i (t_l f_i)` and
  `(t_l f_i) e_i`, which cancels. Also `t_l e_i - e_i t_l = ⟨α_i, y_l⟩ e_i`
  (`WeightGraded.IsScalarOn.commutator`). With `trace (e_i f_i) = 1` this
  gives `Mk a = ck α_i`, hence `a = Mik · ck α_i`. So `τ a` acts on `W μ` by
  `ck μ ⬝ (Mik · ck α_i)`, which is the image of `F(μ, α_i)` in `k`
  (`Hyp.form_cast`).
- `sum_form_root_eq_zero`: `∑_i F(μ, α_i) = 0`. Negation of roots is a
  permutation `σ` of `J` (`exists_neg` and `root_injective`). Reindexing the
  sum by `σ` negates it, so it vanishes.
- `sum_t_mul_td_apply`: `∑_j t_j t^j` acts on `W μ` by `F(μ, μ)`, since
  `t_j t^j` acts by `⟨μ, y_j⟩ (Mik · ck μ)_j`.
- `trOn_e_mul_f`: one step of the recursion,

  `trOn (V ⊓ W μ) (e_i f_i) = trOn (V ⊓ W (μ + α_i)) (e_i f_i) + F(μ, α_i) n(μ)`.

  Write `e_i f_i = f_i e_i + [e_i, f_i]`. By `trOn_mul_comm`, the trace of
  `f_i e_i` on `V ⊓ W μ` equals the trace of `e_i f_i` on `V ⊓ W (μ + α_i)`.
  The commutator acts on `V ⊓ W μ` by `F(μ, α_i)`.
- `trOn_e_mul_f_eq_sum`: iterating `d` times,
  `trOn (V ⊓ W μ) (e_i f_i) = ∑_{j < d} F(μ + j α_i, α_i) n(μ + j α_i)
  + trOn (V ⊓ W (μ + d α_i)) (e_i f_i)`.
- `trOn_e_mul_f_eq_finsum`:
  `trOn (V ⊓ W μ) (e_i f_i) = F(μ, α_i) n(μ)
  + ∑ᶠ_{j : ℕ} F(μ + (j+1) α_i, α_i) n(μ + (j+1) α_i)`.
  Only finitely many `W` are nonzero. Since `X` is torsion-free and
  `α_i ≠ 0`, there is `N` with `W (μ + j α_i) = 0` for `j ≥ N`
  (`WeightGraded.exists_forall_ge_eq_bot`). Take `d = N + 1` above, so the
  remainder vanishes. Then split off the `j = 0` term and write the rest as a
  finite sum.
- `trOn_casimir`:
  `trOn (V ⊓ W μ) Ω = F(μ, μ) n(μ) + ∑_i trOn (V ⊓ W μ) (e_i f_i)`. Every
  summand preserves `V ⊓ W μ`.
- `exists_casimir_eq_smul`: `Ω` acts on `V` by a scalar `c`.

  Proof. Let `v₀` span `V ⊓ W lam` (hypothesis 15). `Ω` preserves `V` and has
  degree `0`, so `Ω v₀ = c v₀` for some `c`. The subspace
  `V ⊓ ker (Ω - c)` is `g`-stable because `Ω` commutes with `g`
  (`Hyp.commute_casimir`). It contains `v₀ ≠ 0`, so it equals `V` by
  irreducibility (hypothesis 14).
- `casimir_scalar`: the scalar is
  `c = F(lam, lam) + ∑_{i, pos i} F(lam, α_i)`. Take traces on
  `V ⊓ W lam`, which has dimension `1`. If `pos i`, then
  `V ⊓ W (lam + α_i) = 0`, and `trOn_e_mul_f` gives trace `F(lam, α_i)` for
  `e_i f_i`. If not `pos i`, then `f_i` maps `V ⊓ W lam` into
  `V ⊓ W (lam - α_i) = 0`, so `e_i f_i` acts by `0` there.
- `freudenthal_cast`: Freudenthal's identity in `k`,

  `(F(lam, lam) + ∑_{i, pos i} F(lam, α_i) - F(μ, μ)) n(μ)
  = ∑_i ∑ᶠ_{j : ℕ} F(μ + (j+1) α_i, α_i) n(μ + (j+1) α_i)`.

  Compute `trOn (V ⊓ W μ) Ω` in two ways. On one side it is `c n(μ)`. On the
  other it is given by `trOn_casimir` and `trOn_e_mul_f_eq_finsum`. The terms
  `∑_i F(μ, α_i) n(μ)` vanish by `sum_form_root_eq_zero`. Then substitute
  `casimir_scalar`.
- `freudenthal`: the same identity in `ℚ`, by injectivity of `ℚ → k`
  (characteristic zero).

`freudenthalCasimirCoreStatement` introduces the data and hypotheses,
packages hypotheses 1–12 as `Hyp`, and applies `freudenthal`. It rewrites the
statement's `∑ᶠ` over positive `j` and over `J` as the finite sums with `if`
used above (`finsum_eq_if`, `finsum_eq_sum_of_fintype`).

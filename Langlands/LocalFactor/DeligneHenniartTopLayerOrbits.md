# Fixed fields, stabilizers and ramp sums

Helper module for the proof of `TopLayerNormTraceStatement`
(`DeligneHenniartTopLayerProof.md`). It has three groups of auxiliary
results, all proved here.

## Weighted ramp sums

`rampSum c N t = Σ_{i<N} c(i+1) ramp_i(t)` is the published integral of the
step function equal to `c(i+1)` on `(i, i+1]`.

- `rampSum_sub` and `rampSum_const_mul`: linearity in the weights.
- `rampSum_nonneg`: nonnegative weights give a nonnegative sum.
- `sub_le_rampSum_sub`: if all weights are at least `1` and
  `0 ≤ y ≤ x ≤ N`, then `x - y ≤ rampSum c N x - rampSum c N y`. The proof
  uses `Σ_{i<N} ramp_i(u) = u` on `[0, N]` (`sum_ramp_eq`) and monotonicity
  of each ramp.
- `rampSum_pos`: nonnegative weights with `c(i₀+1) > 0`, `i₀ < N` and
  `t > i₀` give a positive sum, since the term `c(i₀+1) ramp_{i₀}(t)` is
  positive.

## Fixed fields as p-adic fields

Let `M/K` be finite with `Gal(M/K)` acting. For a subgroup `J`:

- `fixedPadicField J` is the fixed field `IntermediateField.fixedField J`,
  packaged as a `PadicField`. It is finite over `Padic p` because it is
  finite over `K`.
- `range_restrictScalarsHom_fixedPadicField`: the automorphisms of `M` over the
  fixed field, viewed in `Gal(M/K)`, form exactly `J`. This is the Galois
  correspondence `IntermediateField.fixingSubgroup_fixedField`.
- `lowerGroupOrder_fixedPadicField`: the `i`-th lower group of `M` over the
  fixed field has order `|J ∩ G_i|`, with `G_i = lowerRamificationGroup TM K i`.
  It uses the published `lowerRamificationGroup_subfield_eq_comap`.
- `sum_algEquiv_apply_eq_card_mul_trace` (for `M/K` Galois): for `z` in the
  fixed field, `Σ_{σ ∈ Gal(M/K)} σ z = |J| · Tr_{F/K}(z)`. The proof combines
  `trace_eq_sum_automorphisms` for `M/K` with `Algebra.trace_trace`,
  `Algebra.trace_algebraMap` and `[M : F] = |J|`
  (`IntermediateField.finrank_fixedField_eq_card`).

## Stabilizers of finite subsets

Let `G` be a group acting on `X`, `x₀ ∈ X` such that every point is some
`g • x₀`, and `N` a normal subgroup.

- `card_stabilizer_smul_inf`: `|Stab(g • x₀) ∩ N| = |Stab(x₀) ∩ N|`, by
  conjugation by `g`.
- `card_stabilizer_finset_inf_le` (`G` finite): for a nonempty finite
  `S ⊆ X`, `|Stab(S) ∩ N| ≤ |S| · |Stab(x₀) ∩ N|`. Here `Stab(S)` is the
  setwise stabilizer for the pointwise action on finsets. Take `x ∈ S`. The
  orbit of `x` under `T = Stab(S) ∩ N` lies in `S`. The stabilizer of `x` in
  `T` embeds into `Stab(x) ∩ N`. Orbit–stabilizer for `T` then gives the
  bound.
- `le_stabilizer_finset`: if `N ⊆ Stab(x₀)`, then `N` fixes every point
  (normality and transitivity), hence `N ⊆ Stab(S)` for every finite `S`.

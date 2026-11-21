# Proof of unramified descent for the refined Weil strata

`Langlands.Henniart.weilUnramifiedDescentCount` proves the published proposition
`Langlands.Henniart.WeilUnramifiedDescentCountStatement` (module
`Langlands.Correspondence.HenniartWeilElementaryLayer`). It holds at independent
universe levels `uK` and `uW`, with no further hypotheses. The source is Henniart
(1988), Proposition 2.2, as stated in the operator route note (Proposition
`prop:unram` in the form of Proposition `prop:tworeductions`(a)). The route here is a
Clifford-theoretic count over the inertia types of `W_K`.

The geometric Frobenius `φ = localGeometricFrobenius K` fixes the split degree datum
`weilSplit K φ _`. Its inertia types carry the Frobenius conjugation action
`conjType`.

## Part (a)

Let `c` lie in `W_K(k + 1, s, f)`, represented by a class `σ` of torsion number `f`.

- `weilTorsionNumber_pos_dvd_rank` (module `HenniartUnramified/Torsion`) gives
  `0 < f` and `f ∣ k + 1`.
- `dvd_of_mem_weilRefinedStratum` (module `HenniartUnramified/Strata`) gives `f ∣ s`.

## Part (b)

Write `f = m + 1`, `r = (k + 1)/f` and `t = s/f`, so that `f r = k + 1` and `f t = s`.
Since `r ≥ 1`, write `r = r' + 1`. Let `G` be the set of classes of types of dimension
`r` with `r · break = t` (`goodTypes`), and let `mp` be the minimal period for
`conjType 1`.

1. Fixed counts. For each `j + 1 ∣ f`, apply the hypothesis of the statement to the
   unramified extension `(unramifiedStage K (j + 1)).asPadicField`. Its embedding
   satisfies `IsUnramifiedOfDegree` and its residue cardinality is `q^(j+1)` (module
   `HenniartUnramified/Degree`). With `encard_fixed_goodTypes` this gives
   `encard {x ∈ G | conjType (j + 1) x = x} = τ(r, t; q^(j+1))`.
2. Finiteness. For `j + 1 = f` this set `Z` is finite. Every set used below is a
   subset of `Z`, described by a condition on `mp` (a class is fixed by
   `conjType n` exactly when `mp ∣ n`).
3. Möbius. `encard_period_goodTypes` gives
   `encard W_K(k + 1, s, f) · f = #{x ∈ Z | mp x = f}`. `moebius_count` writes the
   right side as `Σ_{i ∣ f} μ(f/i) · τ(r, t; q^i)`.
4. Polar formula. `polar_moebius_of_le` identifies this sum with
   `f · ν(k + 1, f, s; q)`, using the published `polarPartClosedFormula`.
5. Conclusion. The left side is therefore finite, and cancelling `f` gives
   `encard W_K(k + 1, s, f) = ν(k + 1, f, s; q)`.

The supporting modules are in `Langlands/Correspondence/HenniartUnramified/`, each
with its own paired Markdown:

- the abstract coinduction theory, from `SplitDegree` to `Occurs`;
- its local Weil instantiation: `Concrete`, `Period` and `Occurrence`;
- the counting steps: `Arith`, `Fixed` and `Strata`;
- the earlier modules `Torsion`, `Degree` and `Swan`.

The only axioms used are `propext`, `Classical.choice` and `Quot.sound`.

# The fibre average in Herbrand's theorem

Module `Nyll.ValuedFieldTheory.Ramification.Herbrand.Average`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

This file does the finite-group calculation that finishes the proof of Herbrand's theorem on quotients. A non-archimedean depth on a finite group `G` (a `NonarchimedeanDepth`) and a normal subgroup `H` give a filtration of `H`, `H_n = {τ ∈ H : depth τ ≥ n + 1}`. For a nontrivial class `q ∈ G/H` the file defines the normalized average of the depths over the fibre of `q`, and identifies it, at a representative of maximal depth, with the Herbrand function of the filtration of `H`.

## Main definitions and results

- `depth_inv`: `depth σ⁻¹ = depth σ`, derived from the axioms.
- `depthLowerSubgroup`, `depthLowerFiltration`: the subgroups `H_n` and the filtration they form; normality comes from conjugation invariance of the depth.
- `depthRamificationIndex`: the order `|H_0|`.
- `quotientFiberAverage hq`: for `q ≠ 1`, the sum of the (finite) depths of the elements of the fibre over `q`, divided by `|H_0|`.
- `quotientFiberAverage_sub_one_eq_herbrandFunction_of_maximal`: if `σ` has maximal depth `m` in the fibre, then `average − 1 = φ_H(m − 1)`, where `φ_H` is the Herbrand function of the filtration of `H`. The cases are `m = n + 1` (`…_eq_herbrandValueNat_of_depth_eq_succ`) and `m = 0`, where the average is 0.
- `exists_maximal_representative_quotientFiberAverage`: every nontrivial fibre has such a representative.
- `quotientFiberAverage_ge_herbrandFunction_add_one_iff_exists`: given such a representative (hypotheses `hσq` and `hmax`), for a natural number `s`, the average is at least `φ_H(s) + 1` exactly when the fibre contains an element of depth at least `s + 1`.
- Helpers: `truncatedLowerDepth n τ + 1 = min(depth τ, n + 1)` on `H_0`, and the sum of `min(depth τ, n + 1)` over `H` equals `|H_0|` plus the truncated-depth sum over `H_0`.

## Proofs

On the fibre of `σ` one has `depth(στ) = min(depth τ, depth σ)`, by the maximal-representative identity of `Herbrand.Tower`. So the fibre sum is a sum of truncated depths over `H`, which the integral sum formula for `φ` (from `Herbrand.Function`) evaluates. The threshold equivalence follows from strict monotonicity of `φ_H`.

## Watch for

- Here the "quotient depth" is a definition, the fibre average. The valued-field fact that this average equals the depth of the image in the Galois group of the quotient extension is a separate input; it is not proved or assumed here.
- `depthRamificationIndex` is a ramification index only in name: it is `|H_0|` for the filtration defined by the depth.
- The threshold equivalence is stated only for natural `s`.
- The non-archimedean laws are fields of `NonarchimedeanDepth`, not derived from a valuation.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Ramification/Herbrand/Average.lean`: the Lean file is the source byte for byte (SHA-256 `b11a4ffbb7d20f08804443254566107a50a9f751fc9e55b428c74cbe808fe023`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.

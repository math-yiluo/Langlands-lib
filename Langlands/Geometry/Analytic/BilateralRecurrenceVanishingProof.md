# Proof: vanishing of decaying bilateral multiplication recurrences

Authors: Worker 105 (argument and original Lean proof draft), Worker 972
(adaptation into this proof module and documentation).

## Target

The unapplied theorem

```lean
theorem Langlands.Analytic.bilateral_recurrence_vanishing :
    BilateralRecurrenceVanishingStatement.{u, v}
```

has exactly the published proposition
`Langlands.Analytic.BilateralRecurrenceVanishingStatement.{u,v}` from
`Langlands.Geometry.Analytic.BilateralRecurrenceVanishingStatement` as its
type. It has no parameters or hypotheses of its own, and its two universe
levels `u` (of the scalar field) and `v` (of the algebra) are independent.
The statement module and everything it imports are used unchanged.

The proposition says: for every `K : Type u` with `NontriviallyNormedField K`,
every `A : Type v` with `NormedCommRing A`, `NormedAlgebra K A`,
`CompleteSpace A` and `IsNoetherianRing A`, every `f : A` and every
`c : ℤ → A`, if `c` tends to `0` along the cofinite filter on `ℤ` and
`c (n - 1) = f * c n` for every integer `n`, then `c n = 0` for every integer
`n`. The proof works with the given norm, multiplication, scalar action and
topology of `A`. It uses no completeness of `K`, no ultrametric inequality, no
normalization `‖1‖ = 1`, and no nonzero, reducedness, domain or invertibility
assumption on `A` or `f`. The zero algebra and nilpotent `f` are covered by
the same argument, without case distinctions, and the proof never divides by
`f`.

## The implemented proof

The theorem `bilateral_recurrence_vanishing` introduces all the internally
quantified data and applies the auxiliary theorem
`Langlands.Analytic.bilateral_recurrence_eq_zero`. That theorem takes the
scalar field `K` as an explicit argument (it is needed only to apply the
closed-ideal theorem and to form `K`-linear maps), together with the algebra
instances above, `f`, `c`, the decay hypothesis `hc` and the recurrence
`hrec`, and proves `∀ k : ℤ, c k = 0` as follows.

1. **The decaying-orbit ideal.** Let `I : Ideal A` have carrier
   `{a | f ^ n * a → 0 as n : ℕ → ∞}`. It contains `0`, is closed under
   addition (limits of sums), and under multiplication by any `r : A`,
   because `f ^ n * (r * a) = r * (f ^ n * a)` in the commutative ring `A`.
2. **Closedness and completeness.** The published theorem
   `Langlands.Analytic.isClosed_ideal_of_noetherian_banach` (module
   `Langlands.Geometry.Analytic.ClosedIdealsBanach`), applied with this `K`,
   shows that `I` is closed in `A`. Since `A` is complete, `I` with its
   induced norm is a complete space (`IsClosed.completeSpace_coe`).
3. **Multiplication operators.** For each `n : ℕ`, multiplication by
   `f ^ n` restricted to `I` is a continuous `K`-linear map
   `T n : I →L[K] A`; `K`-linearity is `mul_smul_comm`.
4. **Uniform bound.** For each `a ∈ I` the sequence `T n a = f ^ n * a`
   converges, so its range is bounded
   (`Metric.isBounded_range_of_tendsto`). Mathlib's `banach_steinhaus`, whose
   domain `I` is complete by step 2, therefore gives one real `C` with
   `‖T n‖ ≤ C` for every `n`. Mathlib's theorem needs no completeness of the
   scalar field.
5. **Iterating the recurrence.** Induction on `n`, using
   `f * c k = c (k - 1)`, gives `f ^ n * c k = c (k - n)` for all `n : ℕ` and
   `k : ℤ`.
6. **Every `c k` lies in `I`.** The map `n ↦ k - n` from `ℕ` to `ℤ` is
   injective, so it sends `atTop` into the cofinite filter. Composing with the
   decay of `c` gives `f ^ n * c k = c (k - n) → 0`. This is the only use of
   decay along negative indices.
7. **The estimate.** For `n : ℕ`, step 5 at `k + n` gives
   `c k = f ^ n * c (k + n) = T n (c (k + n))`, so
   `‖c k‖ ≤ ‖T n‖ * ‖c (k + n)‖ ≤ C * ‖c (k + n)‖`
   (operator-norm bound `le_opNorm`; the norm on `I` is the norm of `A`).
8. **Conclusion.** The map `n ↦ k + n` is injective, so decay along positive
   indices makes `C * ‖c (k + n)‖` tend to `0`. Passing to the limit in the
   inequality of step 7 gives `‖c k‖ ≤ 0`, hence `c k = 0`. The sign of `C`
   plays no role.

The module imports only the statement module (which already imports the
closed-ideal module and Mathlib's Banach–Steinhaus file) and
`Mathlib.Analysis.Normed.Group.Bounded`. A development check of the final
theorem reports level parameters `[u, v]` and only the axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Provenance and scope

The argument via the closed ideal of elements with decaying forward orbit and
the uniform boundedness principle is internal derived mathematics due to
Worker 105. It is not attributed to an external source. The two tools it uses
are the published Library theorem `isClosed_ideal_of_noetherian_banach` and
Mathlib's `banach_steinhaus`.

This module proves only the stated vanishing of bilateral recurrences. It
establishes no Laurent coefficient normal form, no annulus injectivity or
other annulus statement, and no gluing theorem; those remain separate
obligations of the binary Laurent argument for which this lemma is intended.

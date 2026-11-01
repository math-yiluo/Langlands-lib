# Renard C.I: proof of the actual nilpotent maximum floor recurrence

The theorem `Langlands.Renard.nilpotentDimensionFloorRecurrence` proves
exactly the published closed proposition
`Langlands.Renard.NilpotentDimensionFloorRecurrenceStatement`. For every
natural generator count `l ≥ 1` and dimension `k ≥ 1`, put

```text
q = (k : ℝ) - (nilpotentGeneratedPhi l k : ℝ) / (k : ℝ).
```

The theorem proves all three conclusions: `0 ≤ q`, `Nat.floor q < k`,
and

```text
nilpotentGeneratedPhi l k ≤
  nilpotentGeneratedPhi l (Nat.floor q) +
  nilpotentGeneratedPhi (l - 1) k.
```

The quotient and subtraction defining `q` are real operations.
`nilpotentGeneratedPhi` is the published actual maximum over commuting
nilpotent tuples on `Fin k → ℂ`; its unital adjoin includes the identity
and scalars without counting an extra generator. The theorem has no
additional mathematical premise.

## Source and provenance

The governing source is David Renard, *Représentations des groupes
réductifs p-adiques*, French edition dated 9 July 2026, Appendix C.I,
printed pp.275–276 / one-based PDF281–282. The registered original is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
Worker 1200 read both pages and visually checked PDF281.
The last display on PDF281 is the weak floor recurrence proved here.
The nonnegativity and strict descent conclusions are derived details
that justify its floor convention and the induction on PDF282.

The supplementary registered source
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was read on PDF18–19. Its corrections concern the older printed
pp.317–318. In particular, its strict-counterexample chain differs
from the 2026 text; the proof here follows the 2026 weak recurrence.

Worker 709 authored the shared conditional assembly draft. Worker 1200
reused its arithmetic and assembly, replaced the two explicit proof
inputs by the independently published theorems, and prepared this exact
proof and English explanation. All imported Library modules are used
unchanged.

## Nonnegative argument and strict descent

The private helper `floorArgument_bounds` works for every natural `l`
and every `k ≥ 1`. It specializes
`nilpotentGeneratedMaxDimension_le` to `Fin k → ℂ` and obtains
`nilpotentGeneratedPhi l k ≤ k²`. Casting to the reals and dividing
by the positive real `k` gives `nilpotentGeneratedPhi l k / k ≤ k`,
hence `0 ≤ q`.

The canonical monotonicity conjunct of
`nilpotentDimensionMonotonicity` compares dimension one with dimension
`k`. The dimension-one conjunct of `nilpotentDimensionBaseCases` then
gives `1 ≤ nilpotentGeneratedPhi l k`. Thus the real quotient is
strictly positive and `q < k`. Mathlib's `Nat.floor_lt`, applied with
the proved nonnegativity, gives `Nat.floor q < k`. This is the strict
decrease of the dimension index needed for induction with the same
generator count; no induction hypothesis is used in this proof.

## One maximizing tuple and its own complement

The main proof writes the positive generator count as `n + 1`.
It applies `nilpotentMaximizingComplement.{0}` on `Fin k → ℂ` to
choose a commuting nilpotent tuple `a` attaining
`nilpotentGeneratedPhi (n + 1) k`. It also chooses a complement `W`
to that tuple's own first ideal-power subspace
`NilpotentFiltration.idealPowerSubspace a 1`. Set `s = finrank ℂ W`.
The theorem's bound for this very complement gives

```text
nilpotentGeneratedPhi (n + 1) k ≤ s * k.
```

The published maximizing-complement proof obtains its witness by
attainment and carrier transport and uses the per-tuple restriction
proof for its bound. This assembly consumes that actual theorem.

Next, `nilpotentHeadTailDimension.{0}` is applied to the same `a`,
its commutation and nilpotence proofs, and the same `W` and
complementarity proof. Its final conjunct, rewritten using the
attained maximum equality, gives

```text
nilpotentGeneratedPhi (n + 1) k ≤
  nilpotentGeneratedPhi n k +
  nilpotentGeneratedPhi (n + 1) (k - s).
```

This imported theorem implements the tail-algebra and head-ideal
splitting and the first-level restriction comparison. Complementarity
identifies the dimension of the first ideal-power subspace with `k-s`.
Neither invariance of `W` nor a separately chosen maximizing tuple is
required.

Since `W` is a submodule of the canonical carrier, `W.finrank_le`
gives `s ≤ k`. Therefore the real cast of the natural subtraction
`k-s` is the real difference `k-s`. Dividing the maximum bound by
positive `k` yields `nilpotentGeneratedPhi (n + 1) k / k ≤ s`;
subtracting from `k` gives `(k-s : ℕ) ≤ q` after casting.
With `0 ≤ q`, Mathlib's `Nat.le_floor_iff` gives
`k-s ≤ Nat.floor q`. The canonical dimension monotonicity theorem
then bounds the second term in the preceding display by
`nilpotentGeneratedPhi (n + 1) (Nat.floor q)`.
Natural-number arithmetic combines these inequalities and reorders
the two summands. The predecessor `(n + 1) - 1` is `n`, so this is
the exact target recurrence.

## Boundary cases and scope

For `l = 1`, the reindexing has `n = 0`, and the head/tail theorem
still applies: its tail tuple is empty and its tail algebra is the
scalar algebra. The tail maximum `nilpotentGeneratedPhi 0 k` is `1`
for positive `k`, as proved by `nilpotentDimensionBaseCases`. No
nonempty-tail hypothesis enters the argument.

The floor index may be zero. The actual zero-dimensional value
`nilpotentGeneratedPhi l 0 = 0` is included in the published base
cases, and dimension monotonicity allows that index. In particular,
when `k = 1`, the base case gives `q = 0`, and the three conclusions
reduce to `0 ≤ 0`, `0 < 1`, and `1 ≤ 0 + 1`. The uniform proof
includes this instance.

This pair proves the floor recurrence and its two arithmetic
conclusions. The normalized numerical contradiction, final power-bound
assembly, arbitrary joint blocks and other whole-book obligations
remain separate units.

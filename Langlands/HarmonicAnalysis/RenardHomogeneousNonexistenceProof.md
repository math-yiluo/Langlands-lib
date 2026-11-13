# Renard II.3.9: untwisted invariant distributions need not exist (proof)

The module `Langlands.HarmonicAnalysis.RenardHomogeneousNonexistenceProof`
proves

```lean
theorem Langlands.HarmonicAnalysis.HomogeneousFunctions.Renard.nonexistence :
    NonexistenceStatement
```

whose type is exactly the published
[`NonexistenceStatement`](RenardHomogeneousNonexistenceStatement.md). The
statement has no universe parameters, and neither has the theorem. The module
imports that statement module and three Mathlib modules:
`Mathlib.Algebra.Group.MinimalAxioms` (for `Group.ofLeftAxioms`),
`Mathlib.NumberTheory.Padics.ProperSpace` (local compactness of `ℚ_[2]`) and
`Mathlib.Topology.MetricSpace.Ultra.TotallySeparated` (total disconnectedness
of ultrametric spaces). The statement pair and every pair it imports are
unchanged. The only axioms used are `propext`, `Classical.choice` and
`Quot.sound`.

The source, David Renard, *Représentations des groupes réductifs p-adiques*
(French version dated 9 July 2026, II.3.9, printed p.48 / PDF p.54, first
paragraph), only warns that an invariant measure need not exist. The proof
below supplies a concrete witness; it is not taken from the source. It is the
standard example of the affine group of a nonarchimedean field acting on that
field. (Heuristically, the modular function of the affine group is nontrivial
on the linear subgroup, whose own modular function is trivial; the Lean proof
uses no Haar measure or modular function.)

All helper declarations live in the namespace
`Langlands.HarmonicAnalysis.HomogeneousFunctions.Renard.Nonexistence`.

## The group `G`

`AffineTwo` is a type synonym (a `def`, so that no instance of `ℤ × ℚ_[2]`
leaks onto it) for `ℤ × ℚ_[2]`. Its point `mk n b` stands for the affine map
`x ↦ 2 ^ n * x + b` of `ℚ_[2]`; `power` and `offset` are the two coordinates,
and `ext'` says a point is determined by them.

- Multiplication is `(n, b) * (m, c) = (n + m, 2 ^ m * b + c)`, the
  composite "first `(n, b)`, then `(m, c)`". The identity is `(0, 0)` and the
  inverse is `(n, b)⁻¹ = (-n, -(2 ^ (-n) * b))`. The `@[simp]` lemmas
  `power_mul`, `offset_mul`, `power_one`, `offset_one`, `power_inv` and
  `offset_inv` hold by `rfl`.
- The `Group` instance is `Group.ofLeftAxioms`. Associativity of the offset
  is `zpow_add₀` (with `2 ≠ 0`) followed by `ring`. The left inverse law uses
  `two_zpow_mul_neg : 2 ^ n * 2 ^ (-n) = 1` and `linear_combination`.
- The topology is the product topology of `ℤ × ℚ_[2]` (`inferInstanceAs`),
  and so are the `T2Space`, `LocallyCompactSpace` and
  `TotallyDisconnectedSpace` instances; `ℚ_[2]` gets them from its metric,
  its proper-space instance and its ultrametric.
- `IsTopologicalGroup`: both multiplication and inversion are written through
  `mk`, `power` and `offset`, which are continuous (`continuous_mk'`,
  `continuous_power`, `continuous_offset`), and the exponent map
  `n ↦ 2 ^ n` is continuous because `ℤ` is discrete
  (`continuous_two_zpow`).
- `isLocallyProfinite` is `Langlands.Topology.isLocallyProfinite_of_mathlib`
  applied to these three instances, giving the Library predicate
  `Langlands.Topology.IsLocallyProfinite AffineTwo` (Hausdorff with a compact
  open neighborhood basis).

## The closed subgroup `H` and the quotient

`linearSubgroup` is the subgroup `{x | offset x = 0}` of linear maps
`x ↦ 2 ^ n * x`; it is closed (`isClosed_linearSubgroup`) as the zero set of
the continuous map `offset`. `HomogeneousSpace` abbreviates the actual
`Langlands.Induction.LeftQuotient linearSubgroup`, with its quotient
topology.

- `offset_eq_of_rel`: if `QuotientGroup.rightRel linearSubgroup x y`, that is
  `y * x⁻¹ ∈ linearSubgroup`, then `offset x = offset y`. Indeed
  `offset (y * x⁻¹) = 2 ^ (-power x) * (offset y - offset x)` and
  `2 ^ (-power x) ≠ 0`.
- `coordinate : HomogeneousSpace ≃ₜ ℚ_[2]` sends the coset of `x` to
  `offset x` (`Quotient.lift`, continuous by `Continuous.quotient_lift`); its
  inverse sends `b` to the coset of `mk 0 b`, continuous by
  `continuous_quotient_mk'`. The coset of `x` equals that of
  `mk 0 (offset x)` because `x * (mk 0 (offset x))⁻¹` has offset `0`.
- `coordinate_rightTranslate`: in this coordinate the existing homeomorphism
  `Langlands.QuotientIntegration.rightTranslate linearSubgroup g` is the
  affine map `y ↦ 2 ^ power g * y + offset g`; this holds by `rfl` on coset
  representatives.

## The contradiction

- `ballTest` is the existing
  `Hecke.TestFunction.characteristic` of the closed unit ball of `ℚ_[2]`,
  which is clopen (`IsUltrametricDist.isClopen_closedBall`) and compact
  (`isCompact_closedBall`). `ballTest_apply` computes it as
  `if ‖y‖ ≤ 1 then 1 else 0`.
- `quotientTest` is its pullback along `coordinate`
  (`Hecke.TestFunction.pullback`), a test function on `HomogeneousSpace`.
- `doubling` is `rightTranslate linearSubgroup (mk 1 0)`, which is
  `y ↦ 2 * y` in the coordinate.
- `differenceTest` is `pullback doubling quotientTest - quotientTest`, and
  `differenceTest_apply` computes its value at `q` as
  `ballTest (2 * coordinate q) - ballTest (coordinate q)`.
- `differenceTest_nonnegative`: since `‖2‖ < 1` (`norm_two_lt_one`, from
  `Padic.norm_p_lt_one`), `‖y‖ ≤ 1` implies `‖2 * y‖ ≤ 1`, so every value is
  `0` or `1`. Hence `differenceTest` is a real-valued nonnegative test in the
  sense of `Distribution.IsNonnegativeTest`.
- `differenceTest_ne_zero`: at the point `coordinate.symm 2⁻¹` the value is
  `ballTest 1 - ballTest 2⁻¹ = 1 - 0 = 1`, because `‖2⁻¹‖ = ‖2‖⁻¹ > 1`.

The theorem `nonexistence` supplies `G = AffineTwo` with its group,
topology and topological-group instances, `isLocallyProfinite`,
`H = linearSubgroup` and `isClosed_linearSubgroup`. Given a candidate
functional `T` with `Distribution.IsPositive T` and invariance under every
`rightTranslate linearSubgroup g`, invariance at `g = mk 1 0` and
`Distribution.pushforward_apply` (definitionally) give
`T (pullback doubling quotientTest) = T quotientTest`, so
`T differenceTest = 0` by linearity. Strict positivity at the nonzero
nonnegative test `differenceTest` gives `0 < (T differenceTest).re = 0`, a
contradiction. Thus no candidate functional exists; the argument uses no
continuity or measure-theoretic property of `T`.

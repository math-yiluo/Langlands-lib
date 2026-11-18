# Convergence and holomorphy of both real equal-rank Rankin–Selberg integrals

Entry module of an intermediate result of Task 7400, towards
`Langlands.Global.RankinSelbergGlobal.RealPlaceFunctionalEquationStatement`. Authored by
Worker 823. Every declaration is proved, with no axioms beyond Lean's standard ones
(`propext`, `Classical.choice`, `Quot.sound`).

The equal-rank functional equation at a real place compares two integrals over
`N_n(ℝ) \ GL_n(ℝ)`, `n = r + 1`. The first is `Ψ(s; W, W', Φ)`
(`ArchimedeanLocal.realEqualIntegral D W W' Φ`). The second is the dual integral
`Ψ(s; W̃, W̃', Φ̂)` (`ArchimedeanLocal.realEqualDualIntegral b D W W' Φ`), where:
- `W̃ = ArchimedeanLocal.dualFunction (r + 1) W`, that is `W̃(g) = W(w_n ᵗg⁻¹)` with `w_n` the
  long Weyl element;
- `Φ̂ = realFourierTransform b Φ`.

The Library's package `RealJacquet.EqualEquation a b D W W' Φ …` (module
`RealJacquetConventionReduction`) begins with four conjuncts: both integrands are integrable for
`Re s > σ`, and both integrals are holomorphic there. This module proves these four conjuncts,
with one `σ`. This is Jacquet, *Archimedean Rankin–Selberg integrals* (2009), Theorem 2.1(i)
(p. 6) for both sides of the equal-rank functional equation in Theorem 2.1(iii), together with
holomorphy in the region of convergence. The functions are those of the candidate statement
`RealEqualConvergenceStatement` (module `RealEqualConvergence`).

## The statement

`Langlands.Global.RankinSelbergGlobal.RealEqualPairConvergenceStatement : Prop` says the
following. Let `r : ℕ`, `D : RealQuotientMeasureData r`, `a, b : ℝˣ`, `W, W' : GL_(r+1)(ℝ) → ℂ`,
and `Φ` a Schwartz function on `Fin (r + 1) → ℝ`. Assume the four hypotheses of
`RealEqualConvergenceStatement`:
- every iterated right derivative of `W` lies in `RealLocalWhittaker.regularFunctions r a`;
- every iterated right derivative of `W'` lies in `RealLocalWhittaker.regularFunctions r (−a)`;
- for each of `W`, `W'`, all iterated right derivatives are bounded by
  `C · realMatrixHeight(g)^N` with one exponent `N` common to all derivatives.

Then there is `σ` such that, for every `s` with `σ < Re s`:
1. `realEqualIntegrand W W' Φ s` is integrable for `D.measure`;
2. `realEqualIntegrand (dualFunction (r+1) W) (dualFunction (r+1) W') (realFourierTransform b Φ) s`
   is integrable for `D.measure`;

and furthermore:

3. `realEqualIntegral D W W' Φ` is complex differentiable on `{s : σ < Re s}`;
4. `realEqualDualIntegral b D W W' Φ` is complex differentiable on `{s : σ < Re s}`.

The theorem `Langlands.Global.RankinSelbergGlobal.realEqualPairConvergence` proves it.
The parameter `b` is arbitrary. In particular it can be the Fourier parameter `b` of
`EqualEquation a b`.

## Proof structure

The declarations below are in the namespace
`Langlands.Global.RankinSelbergGlobal.RealEqualDualConvergence`. The proof applies the generic
convergence theorem `RealEqualConvergence.exists_convergence` twice:
- to `(W, W', Φ)`;
- to `(W̃, W̃', Φ̂)`.

For the second application it checks the hypotheses of `exists_convergence` for the dual data.
These are continuity, invariance of `W̃ W̃'` under left multiplication by the upper unipotent
group, the gauge estimate `HasGauge` for `W̃` and `W̃'`, and continuity and rapid decay of `Φ̂`.

### The dual function on `torus y · k`

Write `θ(g) = ᵗg⁻¹` (`GeneralLinear.inverseTranspose`) and `w = GeneralLinear.weylLong (r+1) ℝ`.

- `inverseTranspose_torus`: `θ(torus y) = torus(−y)`, since diagonal matrices are symmetric.
- `unitary_inv_val`, `inverseTranspose_unitary`: for orthogonal `k`, `k⁻¹ = ᵗk`, so `θ(k) = k`.
- `weylLong_mem_unitary`: `w` is orthogonal. By the Library, `θ(w) = w` and `w⁻¹ = w`, so
  `ᵗw = w` and `w ᵗw = w² = 1`.
- `weylUnitary k = w k`, an orthogonal matrix. `revNeg y` is `i ↦ −y_(rev i)`, where `rev`
  reverses `Fin (r+1)`.
- `weylLong_torus_weylLong`: `w · torus y · w = torus(i ↦ y_(rev i))`, by the Library's entry
  formula `(w g w)_(ij) = g_(rev i, rev j)`.
- `dual_torus_mul`: `W̃(torus y · k) = W(torus(revNeg y) · w k)`. Proof:
  `w θ(torus y · k) = w · torus(−y) · k = (w · torus(−y) · w⁻¹)(w k)`.
- `rootPos_revNeg`: `rootPos(revNeg y) = rootPos y`. For `y' = revNeg y` and `i < r`,
  `y'_i − y'_(i+1) = y_j − y_(j+1)` with `j = r − 1 − i` (the reversal of `i` in `Fin r`), by
  Mathlib's `Fin.rev_castSucc` and `Fin.rev_succ`. The sum is then reindexed by `Fin.revPerm`.
- `sum_abs_revNeg`: `∑_j |(revNeg y)_j| = ∑_j |y_j|`.

### Hypotheses for the dual data

- `hasGauge_dual`: `HasGauge W` implies `HasGauge W̃`, with the same exponents. Apply the gauge
  bound of `W` at `(revNeg y, w k)` and use the two invariance lemmas.
- `continuous_dual`: `W̃ = W ∘ weylInverseTranspose`, where the Library's
  `GeneralLinear.weylInverseTranspose` is the homeomorphism `g ↦ w θ(g)`.
- `dual_mul_invariant`: if `W(ug) W'(ug) = W(g) W'(g)` for all upper unipotent `u`, then the same
  holds for `W̃, W̃'`. The Library's `Whittaker.weylInverseTranspose_left_unipotent` gives
  `w θ(u g) = u' · w θ(g)` with `u' = Whittaker.reflectedUnipotent u` upper unipotent.
- `fourier_rapidDecay`: `Φ̂` is continuous and has rapid decay. By
  `RealFourierSchwartz.exists_schwartz_eq` it is a Schwartz function, and
  `RealEqualConvergence.hasRapidDecay_schwartz` applies.

### The main theorems

- `exists_pair_convergence`: let `W, W'` be continuous, with `W W'` invariant under the upper
  unipotent group and `HasGauge W`, `HasGauge W'`. Then for every Schwartz `Φ` and every `b`
  the four conclusions hold with one `σ`. `exists_convergence` gives `σ₁` for `(W, W', Φ)` and
  `σ₂` for `(W̃, W̃', Φ̂)`; take `σ = max(σ₁, σ₂)`. The dual integral
  `realEqualDualIntegral b D W W' Φ` is by definition `realEqualIntegral D W̃ W̃' Φ̂`.
- `exists_pair_convergence_of_regular`: the statement's conclusion under its hypotheses. As in
  `RealEqualConvergence.exists_convergence_of_regular`:
  - the empty list of derivatives gives `W ∈ regularFunctions r a` and
    `W' ∈ regularFunctions r (−a)`, and smoothness gives continuity;
  - the character laws and `realWhittakerCharacter_mul_neg` give invariance of `W W'`;
  - `RealWhittakerGauge.exists_gauge_bound` gives `HasGauge W` and `HasGauge W'`.

  Then it applies `exists_pair_convergence`.
- `realEqualPairConvergence : RealEqualPairConvergenceStatement` is
  `exists_pair_convergence_of_regular`.

## Relation to the literature

In Jacquet's setup (pp. 5–6), `W` lies in the `ψ`-Whittaker model of an induced representation
`π_(σ,u)` (and `W'` in a `ψ̄`-Whittaker model, `ψ̄ = ψ⁻¹`). Then the function
`W̃(g) = W(w_n ᵗg⁻¹)` lies in the `ψ̄`-Whittaker model of the induced representation
`π_(σ̃,ũ)`: the character is inverted. Here `σ̃` reverses the order of the inducing blocks and
replaces each block by its contragredient, and `ũ` reverses and negates the twists. Jacquet notes
that the semisimple representations attached to `π_(σ,u)` and `π_(σ̃,ũ)` are contragredient, but
the induced representations themselves need not be contragredient when they are reducible. For
the majorization of `W̃` (p. 17) he uses the twisted representation `π^ι(g) = π(ᵗg⁻¹)` on the
same space, with the linear form `λ ∘ π(w_n)`. If `λ` is a `ψ`-form, this is a `ψ̄`-form for
`π^ι`, and Jacquet applies the gauge estimate of Proposition 3.1 to it. For the second function
of the pair the roles are exchanged: `W̃'` has character `ψ`. The inversion of the character is
the Library's `Langlands.Whittaker.standardCharacter_reflected`: conjugating the inverse
transpose of an upper unipotent matrix by `w_n` reverses and negates its first superdiagonal.
The convergence of the dual integral then follows from the equal-rank argument of §5.1
(p. 32).

The Lean proof uses no representation theory for the dual side. It transfers the gauge estimate
from `W` to `W̃` at the level of functions: `θ` and `w` map `torus y · k` to
`torus(revNeg y) · w k`, and `revNeg` preserves both quantities in the gauge bound. As in
`RealEqualConvergence`, the abscissa `σ` is only shown to exist.

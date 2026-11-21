# Reduction of the joint root-hyperplane form of Eisenstein series

`Langlands.Global.eisensteinJointRootHyperplaneReduction` proves the
proposition `Langlands.Global.EisensteinJointRootHyperplaneReductionStatement`.
At the same number-field universe `u` throughout, it is the implication

```
PositiveChamberNonemptyStatement.{u} →
EisensteinMeromorphicContinuationStatement.{u} →
EisensteinRootHyperplaneStatement.{u} →
EisensteinJointRootHyperplaneStatement.{u}
```

The last proposition concerns any scalar continuation `EP` with a common
holomorphy domain `DP` for all adelic points and agreement with the
Eisenstein series for sufficiently regular real part. In any given complex
linear chart `e`, it asks for a holomorphic pole-cleared family `h(s,g)`
near the given parameter, with nonzero real root forms, joint continuity,
and left `G(F)`-invariance. All hypotheses and conclusions of that
published proposition are retained.

## Implemented proof

**A common agreement region.** A positive parameter makes every real root
functional in the unipotent radical nonzero. The unipotent roots form a
finite set. For any threshold `R`, the ratios of `R` to the values of these
functionals at the real part of the positive parameter have some common
upper bound. Scaling the positive parameter by that bound plus one makes
it `R`-regular. This also covers the empty root set, where regularity is
vacuous. Each such region is open in coordinates by
`isOpen_setOf_isRegularParameter`. Two continuations agreeing with the
series at possibly different thresholds therefore agree on the part of
one nonempty open region in their common holomorphy domain. The helper
`eqOn_of_isMeromorphicOn_of_eqOn_open` applies
`Meromorphic.eq_of_hasLocalDenominators` on the entire coordinate space to
extend this agreement to their whole common holomorphy domain.

**Positive matrix size.** The uniform-growth-valued continuation supplies
`E'` and local meromorphic data for it, with a holomorphy domain in each
local parameter set, and automorphy there. Evaluating that local data by
`UniformGrowthFrechetSpace.evalCLM` and using
`hasLocalMeromorphicData_of_isMeromorphicOn` and
`exists_isMeromorphicOn_of_local` gives one global scalar holomorphy
domain `D₀` in the given chart, common to all `g`. Compare `E'` with `EP`
on `D₀ ∩ e⁻¹(DP)` using the agreement region above.

The scalar root-hyperplane premise gives a single root product `Q` and
neighbourhood `O` of the marked point, with a holomorphic function for
each `g`. Choose these functions as one family `h(s,g)`. On `O ∩ e⁻¹(DP)`
this family equals `Q(s) EP(e(s),g)`. The helper
`exists_joint_region_of_local_meromorphy` uses a local scalar denominator
`q` and weakly holomorphic uniform-growth numerator `a` for the local
Fréchet-valued continuation. Take an open ball about the marked point in
`O` and in the open image of the numerator's domain. Holomorphic
uniqueness keeps `q` nontrivial on the ball. The intersection of the ball
with the local regular domain and `D₀ ∩ e⁻¹(DP)` is dense relative to the
ball. On that intersection the equality of the continuations and
linearity of evaluation give `q(s) h(s,g) = Q(s) ev(a(s),g)`. For fixed `g`
both sides are continuous in `s`, so the identity holds on the ball.
`UniformGrowthFrechetSpace.continuousOn_of_mul_eq_eval` now gives joint
continuity of `h`. The continuation's local automorphy gives left
`G(F)`-invariance of `h` on the same dense intersection, and pointwise
holomorphy extends that identity to the ball. The scalar root-clearing
identity on the whole intersection with `e⁻¹(DP)` is unchanged.

**Matrix size zero.** The closed embedding into adelic `GL₀` makes the
adelic point group a subsingleton. The Eisenstein series has only one
summand; in the given chart its dependence on the parameter is a constant
times the complex exponential of a linear form. It is entire and
independent of the adelic point. The same scalar uniqueness argument gives
agreement with `EP` on `e⁻¹(DP)`, so the conclusion uses the empty root
product with exponent zero and the entire coordinate space. This adapts
the rank-zero argument in `AdelicEisensteinImaginaryContinuation` to
arbitrary `u`.

## Provenance and scope

This is a derived implication between the Library propositions, not a
new formulation of a separate result of Bernstein–Lapid. Their Theorem
2.3 (1), (6) and §8.6 Corollary supply the source context for the
continuation and root-hyperplane formulations; see the paired Markdown of
`AdelicEisensteinJointRootHyperplaneStatement` for the precise source
comparison. The proof uses scalar uniqueness and the Library's
joint-continuity criterion rather than a Fréchet-valued power series or
integral. The three input propositions are hypotheses here. The module
does not prove any of them, the joint root-hyperplane statement without
premises, or holomorphy on the imaginary axis in Lapid's Proposition 6.

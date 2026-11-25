# The real-place functional equation from continuation premises

Internal reduction towards
`Langlands.Global.RankinSelbergGlobal.RealPlaceFunctionalEquationStatement`. All declarations
are proved; no axioms beyond Lean's standard ones are used.

The Library's reduction `realPlaceUniformLocalTheoryReduction` (module
`RealUniformLocalTheoryReduction`) derives the target from three premises:
`RealLocalUniformUnequalJacquetStatement`, `RealLocalUniformPositiveEqualJacquetStatement`
and `RealPlaceContragredientPairLStatement`. The first two require the full packages
`RealJacquet.UnequalEquation` and `RealJacquet.EqualEquation` for functions in
`realUniformWhittakerModel`. Each package (`RealJacquet.EquationPackage`) has nine conjuncts:
integrability of the two integrands on a right half-plane, holomorphy of the two integral
functions there, two meromorphic continuations, agreement with them on the half-plane, and
the multiplied-out functional equation off a discrete set.

The first four conjuncts are proved by `realUnequalPairConvergence` (module
`RealUnequalPairConvergence`) and `realEqualPairConvergence` (module
`RealEqualDualConvergence`). This module removes them from the premises, so only the
continuation and functional-equation parts remain as hypotheses. It is an intermediate
result. It does not prove the continuation, the functional equation or the
contragredient-denominator premise.

## Declarations

In the namespace `Langlands.Global.RankinSelbergGlobal.RealJacquet`:

- `ContinuationPackage Z Zd L Ld E sign`: there are `σ : ℝ` and `M Md : ℂ → ℂ`, meromorphic
  on all of `ℂ`, with `Z s = M s` and `Zd s = Md s` whenever `σ < Re s`, and, for `s`
  outside a discrete set (the filter `Filter.codiscrete ℂ`),
  `L s * Md (1 - s) = sign * E s * Ld (1 - s) * M s`. These are word for word the last five
  conjuncts of `EquationPackage`.
- `EquationPackage.continuation`: an equation package yields its continuation package (same
  `σ`, `M`, `Md`).
- `equationPackage_of_continuation`: if there is `σ₁` such that `K s` is `μ`-integrable and
  `Kd s` is `ν`-integrable for `σ₁ < Re s`, and `Z`, `Zd` are complex differentiable on
  `{s | σ₁ < Re s}`, then `ContinuationPackage Z Zd L Ld E sign` implies
  `EquationPackage μ ν K Kd Z Zd L Ld E sign`. The proof takes `σ = max σ₁ σ₂`, where `σ₂`
  comes from the continuation package, and restricts all half-plane statements to it.
- `UnequalContinuation h a D W W' ds es dds ees b sign` and
  `EqualContinuation a b D W W' Φ ds es dds ees sign`: `ContinuationPackage` applied to
  exactly the functions `Z`, `Zd`, `L`, `Ld`, `E` used by `UnequalEquation` and
  `EqualEquation` with the same arguments. So `UnequalEquation` is `UnequalContinuation`
  plus the four convergence conjuncts, and likewise for the equal rank.

In the namespace `Langlands.Global.RankinSelbergGlobal`:

- `RealLocalUniformUnequalContinuationStatement`: the statement
  `RealLocalUniformUnequalJacquetStatement` with `UnequalEquation` replaced by
  `UnequalContinuation`. The quantifiers, the block lists, the dual block lists
  `ds.map RealLocalJacquet.dualBlock` and `es.map RealLocalJacquet.dualBlock`, the epsilon
  parameter `-a` and the sign `determinant(ds,-1)^(t+1) * determinant(es,-1)` are unchanged.
- `RealLocalUniformPositiveEqualContinuationStatement`: the statement
  `RealLocalUniformPositiveEqualJacquetStatement` with `EqualEquation a (-a) …` replaced by
  `EqualContinuation a (-a) …`, with the same quantifiers (in particular `0 < r`), dual
  block lists and sign `determinant(ds,-1)^r`.
- `realLocalUniformUnequalJacquet_of_continuation`: the unequal continuation statement implies
  `RealLocalUniformUnequalJacquetStatement`. For `W` in `realUniformWhittakerModel r ds a`
  and `W'` in `realUniformWhittakerModel t es (-a)`, the Library theorem
  `realUniformWhittakerRegularity` gives, for each function, that every iterated right
  derivative lies in `RealLocalWhittaker.regularFunctions` (for `a` and `-a`
  respectively) and the uniform derivative growth bound. These are the hypotheses of
  `realUnequalPairConvergence`, which gives the four convergence conjuncts. Then
  `equationPackage_of_continuation` combines them with the premise.
- `realLocalUniformPositiveEqualJacquet_of_continuation`: the same for the equal rank, using
  `realEqualPairConvergence` with additive parameters `a` and `b = -a`.
- `RealPlaceUniformContinuationReductionStatement.{u}`: the two continuation statements and
  `RealPlaceContragredientPairLStatement.{u}` imply
  `RealPlaceFunctionalEquationStatement.{u}`.
- `realPlaceUniformContinuationReduction` proves it: the two theorems above turn the
  continuation premises into the premises of the Library's `realPlaceUniformLocalTheoryReduction`,
  which is then applied.

The module declares local Borel `MeasurableSpace` and `BorelSpace` instances on
`GL_(n+1)(ℝ)`, its upper unipotent subgroup and `LeftUnipotentQuotient n ℝ`, as in the
modules it imports, so that the measurable structures in the conclusions agree with those
in the Library statements. It also sets `backward.isDefEq.respectTransparency false`.

## Relation to the literature

Jacquet (2009), Theorem 2.1 (p. 6), states (i) convergence of the integrals for `Re s ≫ 0`,
(ii) meromorphic continuation, as a holomorphic multiple of `L(s, σ_u ⊗ σ'_u')` bounded at
infinity in vertical strips, and (iii) the functional equations. The continuation statements
of this module ask for the meromorphic continuation of both integral functions and for the
functional equation in the multiplied-out form of `EquationPackage`; they do not ask for the
holomorphic-multiple or vertical-strip assertions of (ii), which `EquationPackage` does not
contain. Part (i), together with holomorphy in the region of convergence, is proved in the
imported modules for both integrals of each functional equation. Provenance is internal: the split of the
package and the reduction are bookkeeping on the Library's own statements.

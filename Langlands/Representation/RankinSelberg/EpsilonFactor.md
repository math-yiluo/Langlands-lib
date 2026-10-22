# Epsilon factors of pairs as relations

Author: Worker 11. This module, in namespace `Langlands.RankinSelberg`, defines
when a nonzero monomial `c q^{-ms}` is the epsilon factor `ε(s, π × σ, ψ)` of
Jacquet--Piatetski-Shapiro--Shalika (JPSS), *Rankin--Selberg convolutions*,
Amer. J. Math. 105 (1983), Theorem 2.7(iii), printed page 391. It does this
for actual representations and for supercuspidal isomorphism classes. The
module states no theorem target. Every lemma in it is proved.

No epsilon function is chosen. The factor is a relation `IsPairEpsilonFactor
... e` on candidate values `e = (c, m) : ℂˣ × ℤ`, read as
`ε(s) = c (q^{-s})^m`. The module proves that at most one `e` satisfies the
relation and that the relation is invariant under equivalence of
representations. It does not prove that some `e` exists. That needs JPSS
Theorem 2.7 (the published targets of `FunctionalEquationStatement`), the
existence of a compatible quotient measure (`QuotientHaarExistenceStatement`),
and nonzero Whittaker functionals.

## Source

JPSS, Theorem 2.7(iii), printed page 391. For `π` on `G_r` and `π'` on `G_t`
of Whittaker type, with `W ∈ W(π; ψ)` and `W' ∈ W(π'; ψ̄)`, there is a factor
`ε(s, π × π', ψ)` of the form `c q^{-ns}`. It satisfies display (1) when
`r = t` and display (2) when `t ≤ r - 1`, for every `j`. The published
`FunctionalEquationStatement` and its Markdown spell out both displays. Its
two conclusions, `EqualRankFunctionalEquationConclusion` and
`UnequalRankFunctionalEquationConclusion`, assert that some `c` and `m` work.
This module makes `c` and `m` parameters.

Henniart, *Caractérisation de la correspondance de Langlands locale par les
facteurs ε de paires*, Invent. Math. 113 (1993), uses `ε(s, π × τ, ψ)` for
supercuspidal `π` and `τ` of ranks `n` and `r < n` (Corollary, printed page
340). The class-level relation below is the form needed there.

## Monomials

These are proved auxiliary results:

- `unitMonomial_eq_of_infinite`: if `c x^m = c' x^{m'}` on an infinite set of
  nonzero complex numbers, then `c = c'` and `m = m'`. The proof multiplies by
  a large power of `x` and compares polynomials.
- `spectralPoint_ne_zero`, `finite_spectralPoint_roots`,
  `finite_reflected_spectralPoint_roots`: for `q > 1`, `q^{-s} ≠ 0`, and a
  nonzero polynomial vanishes at `q^{-t}` or at `q^{-(1-t)}` for only finitely
  many real `t`. They use the published injectivity of `t ↦ q^{-t}` on reals.
- `IsNormalizedGenerator.exists_ne_zero`: a value set with a normalized
  generator contains a nonzero rational function.
- `NormalizedFunctionalEquation.epsilon_unique`: if one nonzero continuation
  `R` satisfies the published `NormalizedFunctionalEquation` with `(c, m)` and
  with `(c', m')`, for the same generators and sign, then `c = c'` and `m = m'`.
  Away from finitely many real `t`, both sides at `s = t` are defined and
  `P(q^{-t}) R(q^{-t}) ≠ 0`. Cancelling gives the monomial identity at
  infinitely many points `q^{-t}`.

## Transport along equivalences

For an actual equivalence `φ : π.Equiv π₂`, `functionalPullback φ ℓ` is the
functional `ℓ ∘ φ`. It is equivariant for the same character, and
`functionalPullback_ne_zero` shows that it is nonzero when `ℓ` is.
`coefficientModel_functionalPullback` proves that both functionals have the
same coefficient image: `g ↦ ℓ(φ(π(g)v)) = ℓ(π₂(g)(φ v))`, and `φ` is
bijective. These lemmas hold for any group, subgroup and character.

## Fixed-monomial functional equations

`EqualRankEpsilonEquation q ψ abv μ ν π σ ℓ ℓ' c m` is the body of the
published `EqualRankFunctionalEquationConclusion` with `c` and `m` taken out
of the existential. So it says: there are `ζ`, `P` and `Pdual` such that `ζ`
is the minus-one scalar of the model of `σ`, `P` and `Pdual` are the
normalized generators of the original and dual values, and every model
vector pair and Schwartz--Bruhat `Φ` satisfies the normalized equation with
the monomial `c (q^{-s})^m`. `UnequalRankEpsilonEquation hnr ...` does the
same for `UnequalRankFunctionalEquationConclusion`, still for every block
`j`. The candidate `π` has rank `r + 1` and the test `σ` rank `n + 1 < r + 1`.

For each of the two equations the module proves:

- `exists_equalRankEpsilonEquation_iff` (and the unequal version): some `(c, m)`
  satisfies the fixed equation iff the published conclusion holds. So nothing
  is lost or added.
- `.congr_model`: the equation depends on `ℓ` and `ℓ'` only through their
  coefficient images. It is proved by unfolding and rewriting. In the unequal
  case, `unequalRankValuesAt_eq` first removes the rank transport by `subst`.
- `.unique`: for `q > 1` and nonzero `ℓ'`, `(c, m)` is unique. The minus-one
  scalar, both generators, the Fourier partner and the continuations are each
  unique by published lemmas. A nonzero value then exists, and
  `epsilon_unique` applies. In unequal rank the block `j = 0` is used.
- `.functionalPullback_iff`: pulling both functionals back along equivalences
  does not change the equation. This is `.congr_model` with the transport
  lemma.

## The relations

The ambient field `F` is a nonarchimedean local field (Mathlib's
`IsNonarchimedeanLocalField`) with a measurable structure. The groups
`GL_{n+1}(F)` and its upper unipotent subgroup carry Borel structures, and the
quotient `N_{n+1} \ GL_{n+1}(F)` (`LeftUnipotentQuotient n F`) carries a
measurable structure. Only the quotient of the test rank `n + 1` occurs.

`IsEqualRankEpsilonFactor q ψ abv ν π σ e` is the conjunction of:

1. `Measure.IsMulRightInvariant (unipotentHaar F n)` holds and a compatible
   quotient measure exists (the published `CompatibleMeasureExists` for
   `generalLinearHaar F n` and `unipotentHaar F n`);
2. `π` has a nonzero functional in `glFunctionals ψ n π`;
3. `σ` has a nonzero functional in `glInverseFunctionals ψ n σ`, the
   functionals for `ψ̄`;
4. for every compatible quotient measure `μ` and all nonzero `ℓ`, `ℓ'`,
   `EqualRankEpsilonEquation q ψ abv μ ν π σ ℓ ℓ' e.1 e.2` holds.

Conjuncts 1--3 make the universal statement 4 non-vacuous. Without a quotient
measure or a nonzero functional no `e` satisfies the relation, so a missing
object never makes two factors agree. Quantifying over every `μ`, `ℓ` and `ℓ'`
matches the source: both sides of each display use the same `dx` on
`N_t \ G_t`, so `ε` does not depend on its scaling, and the Whittaker model
does not depend on which nonzero functional defines it. So uniqueness needs
no uniqueness of compatible quotient measures.

`IsUnequalRankEpsilonFactor hnr q ψ abv ν π σ e` is the same with
`glFunctionals ψ r π` and `UnequalRankEpsilonEquation`.

`IsPairEpsilonFactor q ψ abv ν π σ e`, for a candidate `π` of rank `r + 1` and
a test `σ` of rank `n + 1`, is the unequal relation if `n < r`, the equal
relation if `r = n` (after rewriting `π` along `r = n`), and `False` if
`r < n`. The candidate comes first, as JPSS's `π` on the larger group.

The self-duality `IsSelfDual ψ ν` of the additive Haar measure `ν` is not part
of the relations. The relations are well formed for every additive Haar
measure, but they define the epsilon factor of JPSS and Henniart only when
`ν` is self-dual for `ψ`: both sources use the self-dual measure (JPSS
pp. 377-378, Henniart pp. 339-340). Nothing is asserted about the existence of
a value `e` for any other `ν`. Users state `IsSelfDual ψ ν` as a hypothesis,
as the published functional-equation targets do.

Replacing `ν` by `λ ν` (`λ > 0`) affects the two kinds of relation
differently. The normalized generators do not change, since a nonzero scalar
does not change a Laurent ideal.

- In equal rank `ν` enters only through the row Fourier transform on
  `F^{n+1}`, which is multiplied by `λ^{n+1}`. A value `(c, m)` for `ν`
  becomes `(λ^{n+1} c, m)` for `λ ν`.
- In unequal rank `ν` enters only through the rectangular measures of the
  blocks. The block-`j` integral is multiplied by `λ^{j(n+1)}` and the dual
  block-`k` integral by `λ^{k(n+1)}`, so block `j` alone would need
  `λ^{(k-j)(n+1)} c`. This depends on `j` unless `r = n + 1`. For example for
  a candidate of rank 3 and a test of rank 1 the blocks `(j, k) = (0, 1)` and
  `(1, 0)` need `λ c` and `λ⁻¹ c`, so for `λ = 2` no common value exists. A
  single `(c, m)` for all blocks, as JPSS require, therefore depends on the
  self-dual normalization.
- At adjacent ranks (`r = n + 1`, so `j = k = 0`) both rectangular measures
  are the unit point mass, and the relation does not depend on `ν`.

These scaling remarks explain the role of the hypothesis; they are not proved
in Lean.

The relations take `q` and the absolute value `abv` as parameters. The class
relation below fixes them to the residue cardinality and the normalized
absolute value.

Proved lemmas:

- `IsEqualRankEpsilonFactor.unique`, `IsUnequalRankEpsilonFactor.unique`,
  `IsPairEpsilonFactor.unique`: for `q > 1`, two values satisfying the
  relation are equal. Conjuncts 1--3 provide `μ`, `ℓ`, `ℓ'`, and the
  fixed-equation uniqueness applies.
- `.of_equiv` and `.congr_equiv` for all three: for equivalences
  `π ≃ π₂` and `σ ≃ σ₂` the relations agree. The functionals of `π₂` come from
  pulling back along `φ.symm`. Conversely every nonzero functional of `π₂` is
  pulled back to a nonzero functional of `π`.
- `isPairEpsilonFactor_of_lt`, `isPairEpsilonFactor_self` and
  `not_isPairEpsilonFactor_of_lt` unfold the case split.

## Supercuspidal classes

`IsClassEpsilonFactor F ψ ν π τ e` is for a p-adic field `F : PadicField p` with
its canonical topological data `F.canonicalTopologicalData`, an additive
character `ψ`, an additive Haar measure `ν`, a class `π` in the published
`PadicField.SupercuspidalClass F (r + 1)` (carriers in universe `uV`) and a
class `τ` in `PadicField.SupercuspidalClass F (n + 1)` (carriers in universe
`uW`). It installs the canonical topology, valuative relation and
local-field structure, and the Borel structures, as the published targets do.
It then lifts `IsPairEpsilonFactor` with `q` the residue cardinality
`F.canonicalTopologicalData.residueCardinality` and the absolute value the
published `normalizedAbsoluteValue` to pairs of isomorphism classes. The lift
is well defined by `IsPairEpsilonFactor.congr_equiv` and the published
`SmoothRep.equivOfIso`.

- `isClassEpsilonFactor_mk`: on representatives it is the pair relation
  (`Iff.rfl`).
- `IsClassEpsilonFactor.unique`: the class epsilon factor is unique, using the
  published `residueCardinality_gt_one`.

The relation does not assume genericity. A supercuspidal representation has a
nonzero Whittaker functional (published `SupercuspidalKirillovStatement`, not
proved), and without one no `e` satisfies the relation.

## Lean checks

The module compiles with `lean_check` in environment `3b864ddf` with no errors
or warnings. `IsClassEpsilonFactor` was inspected: it returns `Prop`, has
universe parameters `uF uV uW`, and uses only `propext`, `Classical.choice` and
`Quot.sound`. There is no `sorry` and no new axiom.

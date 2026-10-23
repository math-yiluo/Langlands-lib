# Henniart's supercuspidal local converse theorem

Author: Worker 11. This module, in namespace `Langlands.RankinSelberg`, states
the Corollary of Henniart, *Caractérisation de la correspondance de Langlands
locale par les facteurs ε de paires*, Invent. Math. 113 (1993), printed page
340, as the theorem target `SupercuspidalLocalConverseStatement`. Defining the
target asserts nothing. The module also defines the hypothesis of the
Corollary for supercuspidal classes and for actual representations. Its
representative-agreement lemma is proved; the individual factor bridge is
reused from `EpsilonFactor`.

The epsilon factors are the relation `IsClassEpsilonFactor` (and on actual
representations `IsPairEpsilonFactor`) of the published module
`Langlands.Representation.RankinSelberg.EpsilonFactor`. That relation says
when a candidate value `e = (c, m) : ℂˣ × ℤ` is the factor
`ε(s, π × τ, ψ) = c (q^{-s})^m` of Jacquet--Piatetski-Shapiro--Shalika
(JPSS), *Rankin--Selberg convolutions*, Amer. J. Math. 105 (1983), Theorem
2.7(iii), printed page 391. No epsilon function is chosen here.

## Source

Henniart 1993, Section 1.1 (printed pages 339-340). `F` is a nonarchimedean
local field with residue field of cardinality `q`, and `ψ` is a nontrivial
additive character of `F`. The factors `ε(π × τ, s, ψ)` are those of JPSS, with
the Haar measure on `F` that is self-dual for `ψ` understood (pages 339-340).

Corollary (printed page 340). Let `n ≥ 2`, and let `π` and `π'` be two
irreducible admissible supercuspidal representations of `GL_n(F)`. Suppose that
for every integer `r` with `1 ≤ r ≤ n - 1` and every irreducible admissible
supercuspidal representation `τ` of `GL_r(F)`,
`ε(π × τ, s, ψ) = ε(π' × τ, s, ψ)`. Then `π` and `π'` are equivalent.

Henniart derives the Corollary from his Theorem 1.1 (gamma factors of generic
representations against generic representations of `GL_{n-1}(F)`). This module
states only the Corollary. Theorem 1.1 and the referee's Remark on the same
page use gamma factors `γ(π × τ, s, ψ)`, not epsilon factors, and are not
stated here. For generic representations that are not supercuspidal, equality
of epsilon factors alone does not give equivalence. For example, two
irreducible unramified principal series of `GL_2(F)` with the same central
character have the same epsilon factors against every character of `GL_1(F)`
(a standard computation, not proved here).

## Definitions and lemmas

The p-adic field is `F : PadicField p` with its canonical topological data
`F.canonicalTopologicalData`. `IsPadicPairEpsilonFactor` installs the
canonical topology, valuative relation, local-field structure and Borel
structures, as `IsClassEpsilonFactor` does; the other definitions are built
from these two. `q` is the residue cardinality
`F.canonicalTopologicalData.residueCardinality`, and the absolute value is the
published `normalizedAbsoluteValue`. `ψ` is a `UnitaryAdditiveCharacter`, which
is continuous and nontrivial by definition. `ν` is an additive Haar measure on
`F`.

- `IsPadicPairEpsilonFactor F ψ ν π σ e` is the published `IsPairEpsilonFactor`
  for actual representations `π` of `GL_(r+1)(F)` and `σ` of `GL_(n+1)(F)`,
  with this `q` and absolute value. It only fixes the parameters.
- The existing `isClassEpsilonFactor_mk`: for supercuspidal representations `A` and `B`,
  `IsClassEpsilonFactor` of their classes is `IsPadicPairEpsilonFactor` of
  their underlying representations after unfolding `IsPadicPairEpsilonFactor`.
  Its proof in `EpsilonFactor` is `Iff.rfl`.
- `SameClassEpsilonFactors F ψ ν k π π'` is the hypothesis of the Corollary for
  classes `π` and `π'` in the published `PadicField.SupercuspidalClass F (k+2)`.
  For every `r ≤ k` and every class `τ` in `PadicField.SupercuspidalClass F
  (r+1)`, some `e` satisfies both `IsClassEpsilonFactor F ψ ν π τ e` and
  `IsClassEpsilonFactor F ψ ν π' τ e`.
- `SameSupercuspidalEpsilonFactors F ψ ν k π π'` is the same condition for
  actual representations `π` and `π'` of `GL_(k+2)(F)` on carriers of one
  universe `uV`. The tests `τ` range over the published
  `GeneralLinear.SupercuspidalRep` of rank `r + 1`, and `IsPadicPairEpsilonFactor`
  is applied to their underlying representations.
- `sameClassEpsilonFactors_mk_iff`: for supercuspidal representations `A` and
  `A'`, the class condition on their classes is the condition on their
  underlying representations. The proof applies the hypothesis to the class of
  each test representation and, conversely, uses `Quotient.inductionOn` on each
  test class; each step uses the definitional equality recorded by the existing
  `isClassEpsilonFactor_mk`.

## The target

`SupercuspidalLocalConverseStatement` says: for every prime `p`, every
`F : PadicField p`, every `ψ`, every `ν` in the published
`LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ`, every
`k`, and all classes `π`, `π'` in `PadicField.SupercuspidalClass F (k+2)`,
`SameClassEpsilonFactors F ψ ν k π π'` implies `π = π'`.

How this matches the Corollary:

- Rank. `n = k + 2`, so `n ≥ 2` is built in. The test ranks `r + 1` for
  `r ≤ k` are exactly `1, ..., n - 1`, both endpoints included.
- Representations. A supercuspidal class is an isomorphism class of actual
  smooth irreducible admissible supercuspidal representations
  (`GeneralLinear.SupercuspidalRep`). So `π = π'` as classes says that the
  representations are equivalent, which is Henniart's conclusion.
- Measure. `ν` ranges over the published `SelfDualHaar` subtype: actual Haar
  measures on `F` that satisfy the published Fourier self-duality predicate
  `IsSelfDual ψ`. This is the measure Henniart and JPSS use. The target does
  not assert that such a measure exists. That is the separate published
  proposition `SelfDualMeasureExists`. If no self-dual measure existed, the
  target would hold vacuously.
- Equality of epsilon factors. The hypothesis asks, for each test class, for
  one value `e` that is the epsilon factor of both pairs. Since
  `IsClassEpsilonFactor` has at most one solution (`IsClassEpsilonFactor.unique`),
  this says that both factors exist and are equal. For self-dual `ν` the
  relation is the JPSS epsilon factor (see the `EpsilonFactor` Markdown).
  Existence of a factor for supercuspidal pairs needs JPSS Theorem 2.7 (the
  published `FunctionalEquationStatement` targets), nonzero Whittaker
  functionals (supercuspidal representations are generic: the published
  `SupercuspidalKirillovStatement`) and a compatible quotient measure.
  The measure prerequisite is proved: `quotientHaarExistence` in
  `RankinSelberg/QuotientHaarExistence` proves
  `QuotientHaarExistenceStatement F T n` for every supplied topological data
  `T` and every `n`, using the all-rank construction in `UnipotentQuotient`.
  The JPSS analytic inputs and supercuspidal genericity remain unproved;
  measure existence alone does not establish factor existence.
  Given that existence, the hypothesis is equivalent to Henniart's equality
  `ε(π × τ, s, ψ) = ε(π' × τ, s, ψ)`. Without it, the hypothesis is stronger,
  and it never makes two missing factors agree.
- Universes. `π` and `π'` have carriers in universe `uV`, and the test classes
  have carriers in universe `uW`. Henniart quantifies over all supercuspidal
  `τ`. The universe `uW` is no restriction:
  `Langlands.padicIrreducibleSmoothSmallRealization` in
  `Smooth/SmallRealizationProof` constructs an equivalent irreducible smooth
  complex representation in any independently prescribed carrier universe.
  Its proof uses a countable basis inside a spanning smooth-vector orbit and
  requires no additional admissibility assumption. The class formulation
  still uses the representative-agreement lemma above and the
  equivalence-invariance of the factor relation.

Scope. Henniart's `F` is any nonarchimedean local field, and his application
(Section 1.2) is to fields of positive characteristic. Here `F` is a p-adic
field, a finite extension of `Padic p`, because the supercuspidal class spaces
and the canonical topological data are published only for `PadicField`.

## Lean checks

The module compiles with `lean_check` in environment `3b864ddf` with no errors
or warnings. `SupercuspidalLocalConverseStatement` was inspected: it is a
definition returning `Prop`, has universe parameters `uF uV uW`, and uses only
`propext`, `Classical.choice` and `Quot.sound`. There is no `sorry` and no new
axiom.

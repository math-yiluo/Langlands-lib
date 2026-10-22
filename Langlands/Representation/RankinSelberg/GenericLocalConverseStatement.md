# Henniart's local converse theorems for gamma factors of pairs

Author: Worker 11. This module, in namespace `Langlands.RankinSelberg`, states
Henniart's Theorem 1.1 and the referee's Remark after it, from Henniart,
*Caractérisation de la correspondance de Langlands locale par les facteurs ε
de paires*, Invent. Math. 113 (1993), printed page 340. The gamma factors are
the relation `IsPadicPairGammaFactor` of the `GammaFactor` module. Nothing is
proved about the statements; the module contains only definitions.

## Source

Henniart 1993, Section 1.1. `F` is a nonarchimedean local field with residue
field of cardinality `q`, `ψ` a nontrivial additive character of `F`, and the
factors `γ(π × τ, s, ψ)` are those of Jacquet--Piatetski-Shapiro--Shalika,
with the Haar measure on `F` self-dual for `ψ` (printed pages 339-340).

- **Theorem 1.1.** Let `n ≥ 2` and let `π`, `π'` be irreducible admissible
  representations of `GL_n(F)`, both generic. Suppose that for every
  irreducible admissible generic representation `τ` of `GL_{n-1}(F)`,
  `γ(π × τ, s, ψ) = γ(π' × τ, s, ψ)`. Then `π` and `π'` are equivalent.
- **Remark** (suggested by the referee, proved in Section 3.5). Let `n ≥ 2` and
  let `π`, `π'` be irreducible admissible generic representations of `GL_n(F)`.
  Suppose that for every `r` with `1 ≤ r ≤ n - 1` and every irreducible
  admissible supercuspidal representation `τ` of `GL_r(F)`,
  `γ(π × τ, s, ψ) = γ(π' × τ, s, ψ)`. Then `π` and `π'` are equivalent.

The Remark adds that it also holds for archimedean local fields; that case is
not stated here.

## Definitions

Throughout, `F : PadicField p` carries its canonical topological data, `ψ` is
a `UnitaryAdditiveCharacter` of `F` (continuous and nontrivial by definition),
and `n = k + 2`, so `n ≥ 2` is built in and `π` and `π'` are
actual representations of `GL_{k+2}(F)` on complex vector spaces `V`, `V'` in
universe `uV`.

`SameGenericGammaFactors F ψ ν k π π'`: for every complex vector space `W` in
universe `uW` and every representation `τ` of `GL_{k+1}(F)` on `W` with
`Whittaker.IsGeneric ψ k τ`, there is a rational function `G` with
`IsPadicPairGammaFactor F ψ ν π τ G` and `IsPadicPairGammaFactor F ψ ν π' τ G`.
The test rank `k + 1 = n - 1` is the one of Theorem 1.1.

`GenericLocalConverseStatement` (Theorem 1.1): for every prime `p`, every
`F : PadicField p`, every `ψ`, every `ν` in the published
`LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ` (Haar
measures self-dual for `ψ`), every `k`, and all `π`, `π'` as above, if
`Whittaker.IsGeneric ψ (k + 1) π`, `Whittaker.IsGeneric ψ (k + 1) π'` and
`SameGenericGammaFactors F ψ ν.val k π π'`, then `Nonempty (π.Equiv π')`.

`SameSupercuspidalGammaFactors F ψ ν k π π'`: for every `r ≤ k` and every
`τ` in the published `GeneralLinear.SupercuspidalRep` of `GL_{r+1}(F)`
(carriers in universe `uW`), some `G` is the gamma factor of both
`(π, τ)` and `(π', τ)`. The test ranks `r + 1`, `r ≤ k`, are exactly
`1, ..., n - 1`.

`GenericSupercuspidalLocalConverseStatement` (the Remark): the same as
`GenericLocalConverseStatement` with `SameSupercuspidalGammaFactors` as the
hypothesis on the gamma factors.

`GammaLocalConverseStatement` is the conjunction of the two statements.

## Interpretation

- **Genericity.** The published `Whittaker.IsGeneric ψ m τ` is irreducibility,
  admissibility, and a nonzero Whittaker functional for the standard character
  of `ψ`. This is Henniart's definition (Section 2.1, printed page 342), where
  genericity does not depend on `ψ`. The gamma relation pairs the
  `ψ`-functionals of `π` with the `ψ̄`-functionals of the test, as in
  `W(τ, ψ̄)` of Henniart's Section 2.2; a generic `τ` has nonzero
  `ψ̄`-functionals (conjugate by `diag(1, -1, 1, ...)`), which is not proved in
  the Library. A supercuspidal representation is generic (Henniart p.342,
  citing Gelfand--Kazhdan; published `SupercuspidalKirillovStatement`, not
  proved); the Remark keeps genericity of `π` and `π'` as a hypothesis, as
  Henniart does, and does not require it of the tests.
- **Equality of factors.** Henniart's `γ(π × τ) = γ(π' × τ)` is expressed as
  one rational function `G` satisfying both relations. The relation has at
  most one solution (`IsPadicPairGammaFactor.unique`), so this is equality of
  the factors whenever they exist. It never makes two missing factors agree,
  so the hypothesis is never weaker than Henniart's. That the factors exist for
  generic `π` and every test (JPSS Theorem 2.7, a compatible quotient measure,
  nonzero functionals) is not proved here; without it the hypotheses could not
  be met.
- **Measure.** The relations are evaluated at a self-dual `ν`, as Henniart
  requires. The targets do not assert that such a measure exists (that is the
  separate published `SelfDualMeasureExists`); without one they would hold
  vacuously. In Theorem 1.1 the ranks are adjacent, where the relation does not
  depend on `ν`; for the smaller test ranks of the Remark it does (see the
  Markdown of `GammaFactor`).
- **Equivalence.** `π.Equiv π'` is a `GL_{k+2}(F)`-equivariant linear
  isomorphism, i.e. equivalence of the representations.
- **Field.** `F` is a p-adic field (a finite extension of `Q_p`), not an
  arbitrary nonarchimedean local field, because the canonical topological
  data, the supercuspidal objects and the self-dual measures are published only
  for `PadicField`.
- **Universes.** `π` and `π'` live in universe `uV` and the tests in universe
  `uW`. An irreducible admissible representation of `GL_m(F)` has countable
  dimension, so it is equivalent to one on a carrier in any universe, and the
  gamma relation is invariant under equivalences between carriers in
  different universes (`IsPadicPairGammaFactor.congr_equiv`). So the fixed
  test universe is no restriction; the countability fact is not proved in the
  Library.

## Lean checks

The module compiles with `lean_check` in environment `3b864ddf` with no errors
or warnings. `GammaLocalConverseStatement` was inspected: it returns `Prop`, has
universe parameters `uF uV uW`, and uses only `propext`, `Classical.choice` and
`Quot.sound`. There is no `sorry` and no new axiom.

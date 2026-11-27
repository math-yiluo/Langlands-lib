# σ-regular nonvanishing of twisted traces from local integrability

The module `Langlands.BaseChange.TwistedTraceRegularNonvanishingReduction` states and proves
that the local integrability of twisted characters implies that twisted traces are detected by
σ-regularly supported test functions.

## Statement

`TwistedTraceRegularNonvanishingFromLocalIntegrabilityStatement.{u, v, uW}` is the implication

`TwistedCharacterLocalIntegrabilityStatement.{u, v, uW} → TwistedTraceRegularNonvanishingStatement.{u, v, uW}`

with the same three universe parameters in the premise and in the conclusion (the field `F`, the
cyclic algebra `E` and the representation space `W`). Both propositions are in the Library:

- `TwistedCharacterLocalIntegrabilityStatement` (module
  `Langlands.BaseChange.TwistedCharacterLocalIntegrabilityStatement`): for a nonarchimedean local
  field `F` of characteristic zero, a cyclic `F`-algebra `E` of group `⟨σ⟩` of order `l` and an
  irreducible admissible representation `τ` of `GL_n(E)` with an isomorphism `A` of `τ` onto `τ^σ`,
  the twisted character `φ ↦ tr(τ(φ) ∘ A)` is represented by a function `Θ`, locally integrable
  for every Haar measure, that is locally constant near every σ-regular element (Clozel 1987,
  Theorem 1; Arthur–Clozel 1989, Chapter 1, Proposition 2.2).
- `TwistedTraceRegularNonvanishingStatement` (module
  `Langlands.BaseChange.TwistedTraceRegularNonvanishingStatement`): in the same situation, for
  every Haar measure `μ` on `GL_n(E)` some Schwartz–Bruhat function `φ` supported in the
  σ-regular set has `tr(τ(φ) ∘ A) ≠ 0`.

The theorem `twistedTraceRegularNonvanishingFromLocalIntegrability` proves the implication.

## Auxiliary results

- `exists_support_subset_ne_zero_of_hasLocalValue`: on a Hausdorff, locally compact, totally
  disconnected space with a measure that is finite on compact sets and positive on nonempty open
  sets, if a distribution `D` has the local value `c ≠ 0` at a point `x` (`HasLocalValue μ D x c`,
  module `Langlands.JacquetLanglands.LocalCharacter`) and `R` is an open set containing `x`, then
  some Schwartz–Bruhat function `f` supported in `R` has `D f ≠ 0`. The proof takes a compact open
  neighbourhood `K` of `x` inside `R` and the neighbourhood of the local value
  (`exists_isCompact_isClopen_subset`), and `f` the indicator of `K`; then
  `D f = c · μ(K)` with `0 < μ(K) < ∞`.
- `exists_twistedDistribution_eq_one`: for a cyclic algebra `E` and an irreducible admissible
  representation `τ` of `GL_n(E)` with a σ-intertwiner `A`, the twisted trace takes the value `1`
  on some test function. The `l`-th iterate of the entrywise action of `σ` is the identity
  (`IsCyclicAlgebra.pow_eq_one`), so `exists_compact_openSubgroup_symm_mem` gives arbitrarily small
  compact open subgroups stable under it, and `exists_twistedDistribution_test_values` (module
  `Langlands.BaseChange.TwistedCharacter.LinearIndependence`, the Hecke-corner argument of
  Arthur–Clozel 1989, Chapter 1, Lemma 6.3) applied to the one-element family `τ` prescribes the
  value `1`.

## Proof of the implication

Fix `F`, `E`, `σ`, `l`, `n`, `τ`, `A` and a Haar measure `μ`, and let `Θ` be the function supplied
by `TwistedCharacterLocalIntegrabilityStatement`.

1. `Θ` is nonzero at some σ-regular `δ`. Otherwise `Θ` vanishes on the σ-regular set, whose
   complement is `μ`-null by the Library theorem `sigmaRegularOpenConull`
   (`SigmaRegularOpenConullStatement`, module `Langlands.BaseChange.RegularSetOpenConull`). Then
   `Θ = 0` almost everywhere, so `tr(τ(f₀) ∘ A) = ∫ f₀ Θ dμ = 0` for the test function `f₀` of
   `exists_twistedDistribution_eq_one`, contradicting `tr(τ(f₀) ∘ A) = 1`.
2. `Θ` is locally constant near `δ`, so by `IsTwistedCharacterFunction.hasTwistedCharacterValue`
   (module `Langlands.BaseChange.CharacterFunction`) the twisted distribution has the local value
   `Θ(δ) ≠ 0` at `δ` for `μ`.
3. The σ-regular set is open (`sigmaRegularOpenConull`) and contains `δ`; a Haar measure is finite
   on compact sets and positive on nonempty open sets. So
   `exists_support_subset_ne_zero_of_hasLocalValue` gives a test function supported in the
   σ-regular set with nonzero twisted trace.

## Sources

This is the argument indicated by Henniart–Lemaire, *Changement de base et induction automorphe
pour `GL_n` en caractéristique non nulle*, Mém. SMF 124 (2011), II.2.8, printed pp. 68–69: the
twisted character of an irreducible σ-stable representation is a locally integrable function,
locally constant on the σ-regular set, and twisted characters of pairwise non-isomorphic
representations are linearly independent as functions on the σ-regular set (Lemme, printed p. 69,
which refers to Arthur–Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the Trace
Formula*, Annals of Math. Studies 120 (1989), Chapter 1, Lemma 6.3, printed p. 52). Local
integrability and local constancy are Arthur–Clozel 1989, Chapter 1, Proposition 2.2, printed
pp. 11–12. The nonvanishing of one twisted character on the σ-regular set is the one-element case
of that linear independence; the Lean proof derives it from the nonvanishing of the twisted
distribution and the nullity of the σ-singular set, instead of from linear independence of
functions.

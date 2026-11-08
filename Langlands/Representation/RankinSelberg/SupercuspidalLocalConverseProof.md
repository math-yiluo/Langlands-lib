# Henniart's supercuspidal local converse theorem (proof)

This module proves `Langlands.RankinSelberg.SupercuspidalLocalConverseStatement.{uF, uV, uW}`
for arbitrary universes `uF`, `uV` and `uW`, as the theorem
`Langlands.RankinSelberg.supercuspidalLocalConverse`. It adds no hypotheses.

## Statement proved

The statement is the Library proposition `SupercuspidalLocalConverseStatement` of module
`Langlands.Representation.RankinSelberg.LocalConverseStatement`. Fix a prime `p`,
`F : PadicField p` with its canonical topological data, a unitary additive character `ψ` of `F`,
the additive Haar measure `ν` on `F` that is self-dual for `ψ`, and `k : ℕ`. Let `π` and `π'` be
classes in `PadicField.SupercuspidalClass F (k + 2)`, on carriers in universe `uV`. Suppose
`SameClassEpsilonFactors F ψ ν.val k π π'`: for every `r ≤ k` and every class `τ` of
`PadicField.SupercuspidalClass F (r + 1)`, on carriers in universe `uW`, some value
`e : ℂˣ × ℤ` is the epsilon factor of both pairs `(π, τ)` and `(π', τ)`. Then `π = π'`.

This is the Corollary of Henniart 1993 (printed page 340) for `n = k + 2 ≥ 2`.

## Proof

The proof is the single term
`supercuspidalLocalConverse_of_completeness supercuspidalProductCompleteness.{uF, uW}`.
It applies one published result to another.

- `supercuspidalLocalConverse_of_completeness` (module
  `Langlands.Representation.RankinSelberg.SupercuspidalGraphReduction`) proves
  `SupercuspidalProductCompletenessStatement.{uF, uW} →
  SupercuspidalLocalConverseStatement.{uF, uV, uW}`.
  It is Henniart's graph argument (sections 3.1 and 3.2):
  1. Gamma multiplicativity turns the equal epsilon factors into equal gamma factors against
     normalized products of supercuspidals.
  2. The relation `S` "the Whittaker functions agree on the mirabolic subgroup" is the graph
     of a bijection by Kirillov theory, and it is stable under the mirabolic subgroup. With
     completeness, `S` is contained in the analogous relation `D` for the dual functions,
     which is functional and stable under the inverse transpose of the mirabolic subgroup.
  3. These two subgroups generate `GL_(k+2)`, so `S` is the graph of an equivalence, and the
     two classes are equal.
- `supercuspidalProductCompleteness` (module
  `Langlands.Representation.RankinSelberg.SupercuspidalProductCompletenessProof`) proves
  `SupercuspidalProductCompletenessStatement.{uF, uW}`. A compactly supported Whittaker test
  function that integrates to zero against the Whittaker coefficients of every normalized
  product of irreducible supercuspidals vanishes. This is Henniart 1993, Lemme 2.1.

The universe `uW` of the test representations is the same in both results.

## Provenance

The target is the Corollary of Henniart, *Caractérisation de la correspondance de Langlands
locale par les facteurs ε de paires*, Invent. Math. 113 (1993), printed page 340 (literature id
`henniart-1993-epsilon-pairs`). The Markdown of the two cited modules explains how their routes
differ from the paper. Worker 1718 wrote this module and `SupercuspidalGraphReduction`.
Workers 1830 and 1832 wrote the completeness proof.

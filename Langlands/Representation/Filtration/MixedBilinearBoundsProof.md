# Mixed bilinear length bounds along actual filtrations

This module proves the published target
`Langlands.MixedBilinear.FiltrationBoundsStatement.{uK, uG, uH, uI, uV, uW}`
from `Langlands.Representation.Filtration.MixedBilinearBoundsStatement`. It is
internal linear algebra and finite induction on the existing constructions in
`Langlands.Representation.Filtration.MixedBilinear` and
`Langlands.Representation.Filtration.ObjectDefinitions`. No original-literature
theorem is transcribed. Neither construction nor the target pair is changed.

The proof adapts the same-group module
`Langlands.Representation.Filtration.InvariantBilinearBounds` to the mixed setting.
The coefficient field `k` is arbitrary. The first argument is a representation of
a monoid `G` and the second one a representation of a separate monoid `H`. The
tests are arbitrary functions `a : I → G`, `b : I → H` and `χ : I → k`. The test
type `I` may be empty, and `a`, `b` and `χ` need not be homomorphisms. All lemmas
use the published argument order `length a b χ ρ σ`. The field, both monoids, the
tests and the two carriers have six independent universe levels.

## Component lemmas

- `length_filtration_step_left`: for an `ObjectRepFiltration` `s` of
  `A : Rep k G` and a position `j : Fin n`, the length on step `j.succ` is at most
  the length on step `j.castSucc` plus the length on the graded representation
  `s.gradedRepresentation j`. The proof applies the published
  `length_le_restrict_add_quotient_left` to the lower step, viewed inside the upper
  step through `lowerInUpper`. The quotient term is the graded representation by
  definition. An explicit equivalence identifies the pulled-back lower step with the
  original lower step: it forgets one subtype wrapper, and its inverse uses the
  monotonicity of the filtration. `length_congr_left` transports the length along
  this equivalence.
- `length_le_sum_left`: the length on `A.ρ` in the first argument is at most the
  sum over `Fin n` of the lengths on the graded representations. An induction on
  `j ≤ n` bounds the length on step `j` by the sum over the first `j` positions. At
  `j = 0` the step is `⊥` by `subrepresentation_zero`, and `length_bot_left` gives
  zero. The successor case splits off the last summand with
  `Fin.sum_univ_castSucc` and uses the step lemma. At `j = n` the step is `⊤` by
  `subrepresentation_last`, and `length_top_left` identifies it with `A.ρ`.
- `length_le_sum_right`: the same bound for a filtration of `B : Rep k H` in the
  second argument. The published `length_flip` exchanges the arguments and the two
  test maps, so `length_le_sum_left` applies with `b` and `a` exchanged and `H` in
  the role of the first monoid. Its summands are then flipped back termwise.
- `length_le_double_sum`: with filtrations `f` of `A` and `g` of `B`, the length on
  `A.ρ` and `B.ρ` is at most the double sum over `i : Fin m` and `j : Fin n` of the
  lengths on `f.gradedRepresentation i` and `g.gradedRepresentation j`. The proof
  applies `length_le_sum_left` to `f` and then `length_le_sum_right` to `g` in every
  summand, using `Finset.sum_le_sum`.
- `length_le_of_single_pair`: if every pair `(i, j)` with `i ≠ i₀ ∨ j ≠ j₀` has
  length zero, two applications of `Finset.sum_eq_single` reduce the double sum to
  the pair `(i₀, j₀)`, and `length_le_double_sum` gives the bound.
- `exists_smul_eq_of_length_le_one`: if `length a b χ ρ σ ≤ 1` and `B₀` is a
  nonzero element of `forms a b χ ρ σ`, every element `B` equals `c • B₀` for some
  `c : k`. A nonzero element rules out length zero, because length zero means the
  module is a subsingleton by `Module.length_eq_zero_iff`. Hence the length is
  exactly one. `Module.length_eq_one_iff` makes the form space a simple module, and
  `IsSimpleModule.span_singleton_eq_top` shows that `B₀` spans it. Membership of
  `B` in the span of `B₀`, by `Submodule.mem_span_singleton`, supplies `c`.

## Target theorems

- `filtrationLengthBound : FiltrationLengthBoundStatement.{uK, uG, uH, uI, uV, uW}`
  introduces all quantified data and applies `length_le_double_sum`.
- `singlePairLengthBound : SinglePairLengthBoundStatement.{uK, uG, uH, uI, uV, uW}`
  applies `length_le_of_single_pair`.
- `lengthOneProportionality :
  LengthOneProportionalityStatement.{uK, uG, uH, uI, uV, uW}` applies
  `exists_smul_eq_of_length_le_one`.
- `filtrationBounds : FiltrationBoundsStatement.{uK, uG, uH, uI, uV, uW}` is the
  conjunction of the three.

## Edge cases

- Empty test type: nothing in the proof uses an element of `I` or any algebraic
  property of `a`, `b` or `χ`, so the bounds hold for every test family.
- Zero-length filtrations: if `m = 0` or `n = 0`, the double sum is empty or has
  empty inner sums, and it equals zero. For a filtration of length zero the
  induction in `length_le_sum_left` stops at its base case: step `0` is `⊥` by
  `subrepresentation_zero` and also `⊤` by `subrepresentation_last`, so the bound
  reads `length ≤ 0`. No separate argument is needed. `Fin 0` has no positions, so
  the single-pair statement is vacuous there.
- Repeated steps and zero graded quotients are allowed: no lemma assumes that the
  steps are strict or that a graded quotient is nonzero. Every position of both
  filtrations contributes its own summand, so multiplicities are retained.
- Infinite lengths: all lengths are `ℕ∞`-valued `Module.length`. No finiteness
  assumption is made, and the bounds hold in `ℕ∞` even when some summand is `⊤`.
- Proportionality does not assume that a nonzero form exists. If the form space is
  zero, no `B₀` satisfies `B₀ ≠ 0`, and the claim is vacuous.

The module proves only these generic algebraic bounds. Functional-factor
assembly, unequal-rank covariance, the vanishing of source irreducible pairings,
and unequal-rank uniqueness are separate tasks.

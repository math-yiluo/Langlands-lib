# Proof of the explicit-input reduction of Harris's Proposition 4.8

Worker 997 wrote this proof pair under Task 7213
`b517f901-0ac4-4ae4-a08e-b8b88a3b0fec`. The theorem
`Langlands.Global.Harris.proposition48Reduction` has exactly the type
`Proposition48ReductionStatement.{uF, uV}` of
`Langlands.Global.Arithmetic.HarrisProposition48ReductionStatement`, for
arbitrary independent universes `uF` and `uV`. It consumes the published
conjunction of fourteen inputs and concludes the unchanged
`Proposition48Statement.{uF, 0, 0, 0, uV}`. It adds no premise and no
axiom; the inspected axioms are `propext`, `Classical.choice` and
`Quot.sound`. It does not prove any of the fourteen inputs, which remain
hypotheses, so it does not by itself prove Harris's Proposition 4.8.

## Declarations of the module

All are in namespace `Langlands.Global.Harris`.

* `Proposition48Problem.inductionDegree_withCharacters`: for any characters
  `ξ`, `χ`, `χs`, `(Q.withCharacters ξ χ χs).inductionDegree =
  Q.inductionDegree`. It is proved by `rfl`: `withCharacters` is the
  structure update `{ Q with ξ, χ, χs }`, which keeps the fields `E`, `L`
  and their instances, and `inductionDegree` is `Module.finrank Q.E Q.L`.
* `Proposition48Problem.hasSolution_iff`: `Q.HasSolution` is, by unfolding
  (`Iff.rfl`), the existence of `r` and a cuspidal class `c` with
  `Q.IsSolution c`.
* `Proposition48Problem.exists_untwistedSolution_of_child`: the child step
  described below.
* `Proposition48Problem.hasSolution_of_isAuxiliaryValid`: the induction,
  for an abstract branch hypothesis `hBranch`.
* `proposition48_of_hasSolution`: recovery of `Proposition48Statement` from
  the one-place result.
* `proposition48Reduction`: the exact target.

## The well-founded measure

`hasSolution_of_isAuxiliaryValid` proves
`∀ Q : Proposition48Problem.{uF}, Q.IsAuxiliaryValid → Q.HasSolution.{uF, uV}`.
The proof first generalizes to
`∀ n Q, Q.inductionDegree = n → Q.IsAuxiliaryValid → Q.HasSolution`
and runs strong induction on the natural number `n`
(`Nat.strong_induction_on`). The measure is therefore
`Q.inductionDegree = [L : E]`, the normal-closure degree, and not the rank
`[E' : E]` of an individual problem. After substituting `n`, the induction
hypothesis is used in the form: every one-place valid problem `R` with
`R.inductionDegree < Q.inductionDegree` has a solution.

## The rank case split

Since `E'` is a nontrivial finite-dimensional `E`-vector space (both are
number fields), `0 < [E' : E]` by `Module.finrank_pos`. The proof splits on
`1 < [E' : E]` or `[E' : E] ≤ 1`.

* If `[E' : E] ≤ 1`, then `[E' : E] = 1`, and input 1
  (`Proposition48AuxiliaryRankOneStatement`) applied to `Q` and its
  auxiliary validity gives `Q.HasSolution`.
* If `1 < [E' : E]`, input 4 (`Proposition48MackeyStepStatement`) gives an
  intermediate field `D` with `Q.IsPrimeCyclicStep D`, the alternative
  `Nat.card (Q.MackeyIndex D) = 1 ∨ Nat.card (Q.MackeyIndex D) = [D : E]`,
  and for every `a : L ≃ₐ[E] L` an actual raw child `R` with
  `Q.IsAuxiliaryMackeyChild D a R`, auxiliary validity at the parent's
  parity `[E' : E] - 1`, rank `[R.E' : R.E] = Q.mackeyRank D a` and
  `R.inductionDegree < Q.inductionDegree`. The branch hypothesis is then
  applied to `Q`, `D`, the validity, the prime cyclic step, the cardinality
  alternative, and the child data produced by
  `exists_untwistedSolution_of_child` for each `a`.

## Each child: normalize, induct on the same fields, untwist

`exists_untwistedSolution_of_child` takes the normalization input 2, the
untwist input 3, the induction hypothesis and one raw child `R` with the
four properties above. Input 2 applied to `R` at parity `[E' : E] - 1`
gives `ν : HeckeCharacter R.E` and `χs` with
`R.IsAuxiliaryParityNormalization ([E' : E] - 1) ν χs`. Its last conjunct
is auxiliary validity of the corrected problem
`R.withCharacters (R.correctedCharacter ν) χs χs` (at that problem's own
rank parity). By `inductionDegree_withCharacters` the corrected problem has
the same induction degree as `R`, hence strictly smaller than `Q`'s, so the
induction hypothesis gives `r` and `c` with
`(R.withCharacters (R.correctedCharacter ν) χs χs).IsSolution c`. Input 3,
applied to `R`, the raw validity, the normalization and this solution,
gives actual realizations `S` and `T` with `T.isoClass = c` and
`R.IsUntwistedSolution ν S T`. The lemma returns
`ν, χs, r, S, T` together with the child relation, raw validity, rank,
degree inequality, normalization and untwisted solution: exactly the
existential premise shared by the prime and singleton branch statements.
The equality `T.isoClass = c` is not needed further.

## The branches

In `proposition48Reduction` the fourteen conjuncts are destructured and
the branch hypothesis is discharged by cases on the cardinality alternative:

* `Nat.card (Q.MackeyIndex D) = 1`: input 6
  (`Proposition48SingletonBranchStatement`) applied to inputs 7
  (Theorem 1.2), 9 (spectral rigidity), 10 (isobaric invariance) and 13
  (stable descent), then to `Q`, `D`, the validity, the prime cyclic
  step, the cardinality equation and the child data.
* `Nat.card (Q.MackeyIndex D) = [D : E]`: input 5
  (`Proposition48PrimeBranchStatement`) applied to inputs 7, 8 (local
  comparison), 9, 10, 11 (regular induction), 12 (orbit lift) and 14
  (weak induction supercuspidality), then to the same data.

Inputs 1–4 are used in the induction itself. All fourteen inputs are thus
consumed; none is proved here.

## Recovery of the original four-part output

`proposition48_of_hasSolution` turns the one-place result into
`Proposition48Statement.{uF, 0, 0, 0, uV}`. Given the original data over
fields `E`, `E'`, `L : Type` with normalized reciprocity and
`IsProposition48Datum e χ χs K₀ P Ps ξ`, the proof destructures the datum.
The datum's second conjunct `IsScalarTower E E' L` supplies the scalar
tower instance required by `Proposition48Problem`; the remaining data are
placed unchanged in the bundled problem `Q`. Auxiliary validity of `Q` is
assembled from the datum: normalized reciprocity, the split imaginary
quadratic field, scalar tower, normal closure, `p ∈ Ps.v`, compatibility of
`Ps`, the two unique-place conditions at `Ps.v` and its conjugate, general
position of `χs`, algebraicity at parity `[E' : E] - 1`, relative regularity,
conjugate inversion, and the component `χs` at `Ps`. The conditions on the
primary place `P` and the two place inequalities are discarded; the
datum is not strengthened. Finally `Q.HasSolution.{uF, uV}` is by
definition the original existential conclusion: an index `r` and a
cuspidal class `c` of `GL_{r + 1}(𝔸_E)` that is a weak automorphic induction
of `ξ` (at universes `0, 0, uV`), regular algebraic, conjugate self-dual and
with a supercuspidal component at the auxiliary place `Ps.v`. The first
property implies `r + 1 = [E' : E]` by
`CuspidalOperatorRealization.IsoClass.IsWeakAutomorphicInductionOf.rank_eq`;
the index `r` is one less than the rank. The proof returns the term of
type `Q.HasSolution` with `exact`, so the output is the original one with
no change.

## Provenance

This is the derived organizational reduction described in the paired
Markdown of `Proposition48ReductionStatement`, for M. Harris, *The local
Langlands conjecture for GL(n) over a p-adic field, n < p*, Invent. Math.
134 (1998), 177–210 (`harris-1998-local-langlands`), Proposition 4.8 and its
proof, printed pp.201–203 (`math_9611226v1.tex` lines 1574–1674). The
Lean proof implements the induction that Markdown describes. The one-place
organization, the parity normalization and the untwisting are internal
interfaces of the statement, not claims attributed to Harris. Nothing about
Theorems 1.2 or 1.7, Arthur–Clozel or Henniart–Herb is proved.

`hasSolution_of_isAuxiliaryValid` takes the branch as a hypothesis, not
inputs 5 and 6 themselves, so that the same induction can also prove
`Proposition48ReductionTCStatement`, whose branches have totally complex
foundational premises. That proof is a separate module and is not part of
this one.

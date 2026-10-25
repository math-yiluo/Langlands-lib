# Normalized induction preserves Jordan–Hölder matching

Authors: Worker 250 and Worker 181 (the surjectivity reduction adapts Worker 181's
assembly check).

This module proves the published target
`Langlands.Parabolic.NormalizedInductionFactorMatchingTheorem.{uF,uV,uW}`
from `Parabolic/InductionFactorMatchingStatement`. The theorem is
`Langlands.Parabolic.normalizedInductionFactorMatchingTheorem`, and the
statement is unchanged. Let `σ` and `τ` be smooth complex representations of
the same Levi subgroup whose actual Jordan–Hölder factors match, with
multiplicities, and whose normalized parabolic inductions have finite length.
Then the two normalized inductions have matching actual Jordan–Hölder factors.

The proof has two parts:

- `normalizedInductionFactorMatchingTheorem_of_smoothInductionSurjectivity`
  derives the target from the published proposition
  `Langlands.Induction.SmoothInductionSurjectivityStatement` (module
  `Induction/SurjectivityStatement`) at the two universe triples
  `.{uF,uV,uW}` and `.{uF,uW,uW}`. That proposition is surjectivity of smooth
  induction from a closed subgroup (Bernstein–Zelevinsky 1977, Proposition
  1.9(a)).
- `normalizedInductionFactorMatchingTheorem` applies this conditional theorem
  twice to the published universe-polymorphic proof
  `Langlands.Induction.smoothInductionSurjectivity` (module
  `Induction/SurjectivityProof`).

Mathematically, the argument is the standard one for exact functors. It needs
right exactness of normalized induction. Left exactness alone does not
suffice: the graded pieces of the induced filtration would then only embed in
the inductions of the graded pieces. The proof uses no aggregate exactness
statement and assumes no adjacent-swap or association theorem. Right exactness
is derived here from the generic surjectivity proof.

## Notation

Write `P = B.parabolic F.Carrier` and, for a Levi representation `σ`,
`ρσ = twist (T.parabolicHalfModulus B) (σ.comp (B.leviProjection F.Carrier))`.
This is the inducing representation of `T.normalizedParabolicInduced B σ`, so
the normalized induced object of `σ` is `Rep.of (smoothInduced P ρσ)`.

## Generic smooth-induction part (`Langlands.Induction`)

- `smoothFunctions_ext`, `smoothFunctions_eq_zero_iff`: smooth induced
  functions are determined by their values.
- `valueSubrep P ρ N`: for a linear subspace `N` of the inducing space, the
  subrepresentation of induced functions whose values all lie in `N`. Right
  translation preserves this condition. `valueSubrep_mono`,
  `valueSubrep_bot` and `valueSubrep_top` give monotonicity and the two
  extreme values.
- `valueRestriction P ρ ρ' hρ'`: given a representation `ρ'` on `N` whose
  action agrees with `ρ` (`hρ'`), corestrict an `N`-valued function to an
  element of `smoothInduced P ρ'`. For smoothness, the proof reuses the same
  open subgroup that fixes the original function under right translation;
  no compactness is used. `eval_valueRestriction` holds by `rfl`.
- `nonempty_valueQuotient_equiv`: let `S ≤ N`, and let
  `Q : smoothInduced P ρ' → π` be a surjective intertwiner whose kernel
  consists exactly of the functions with all values in `S`. Then the
  successive quotient of `valueSubrep P ρ S` inside `valueSubrep P ρ N` is
  equivalent to `π`. For surjectivity, a preimage under `Q` is pushed back
  with `smoothInducedMap` of the inclusion `ρ' → ρ`.
- `valueFiltration P ρ N`: given a monotone chain `N` of subspaces from `⊥` to
  `⊤`, the `ObjectRepFiltration` of `Rep.of (smoothInduced P ρ)` with steps
  `valueSubrep P ρ (N i)`. It is built with
  `ObjectRepFiltration.ofSubrepresentations`.

## Generic filtration part (`Langlands.FactorMatchingProof`)

- `nonempty_quotientRep_equiv` (first isomorphism theorem): a surjective
  intertwiner out of the upper step whose kernel is exactly the lower step
  identifies `quotientRep S T` with its target. It uses `Submodule.liftQ` and
  `IntertwiningMap.ofBijective`.
- `subrepInclusion`: the inclusion of a subrepresentation as an intertwiner.
- `exists_hasCompositionSeriesLength_graded`: for a finite filtration of a
  representation of finite length, each graded piece has an actual
  composition series. The published `repLength_eq_sum_of_filtration` writes
  the finite length as a sum of graded lengths, so each summand is finite
  (`ENat.sum_ne_top`). Then `isFiniteLength_iff_exists_compositionSeries` and
  `LengthCriterionProof.hasCompositionSeriesLength_of_compositionSeries`
  give the series.
- `haveSameJordanHolderFactors_of_equiv`: equivalent representations match
  once one of them has a composition series. This is
  `LengthTwo.haveSameJordanHolderFactors_of_equiv`.

## Normalized parabolic part (`Langlands.Parabolic`)

- `NormalizedInducedSurjectivity.{uF,uA,uB} T B` (an internal Prop-valued
  definition): for smooth Levi representations on carriers in universes `uA`
  and `uB`, `T.normalizedParabolicInducedMap B f` is surjective whenever `f` is
  a surjective intertwiner.
- `normalizedInducedSurjectivity_of_smoothInductionSurjectivity`: the generic
  statement at `.{uF,uA,uB}` implies `NormalizedInducedSurjectivity.{uF,uA,uB}`.
  It is applied to `G = GeneralLinear n F.Carrier` and the closed subgroup `P`
  (`B.isClosed_parabolic`). Its hypotheses are discharged as follows:
  - T2: `T.generalLinearT2Space n`.
  - Cofinality of compact open subgroups: `T.generalLinearCompactOpen`.
  - Smoothness of the inflated twisted representations: `isSmooth_comp`
    along `B.leviProjectionContinuous`, then `isSmooth_twist_iff` with
    `T.isOpen_ker_parabolicHalfModulus`.

  The normalized map unfolds definitionally to
  `smoothInducedMap P (B.inducingMap χ f)`, whose underlying function is that
  of `f`. This follows Worker 181's unreviewed assembly check in the shared
  draft of task 501c83dc-cf95-4509-be89-ffebfabc3aa6.
- `nonempty_valueQuotient_equiv_induced`: let `s` be a filtration of a smooth
  Levi representation `σ`, `i` an index, and `φ` an equivalence from the
  graded piece `s.gr i` to a smooth representation `π`. Then the successive
  quotient of `valueSubrep P ρσ (s i.castSucc)` inside
  `valueSubrep P ρσ (s i.succ)` is equivalent to
  `T.normalizedParabolicInduced B π`.
  - Take `ρ'` to be the inducing representation of the step `s i.succ`;
    agreement holds by `rfl`.
  - Take `Q` to be the normalized induced map of `φ ∘ gradedProjection`.
    This map is surjective by `NormalizedInducedSurjectivity`, since the step
    is smooth as a subrepresentation and `φ ∘ gradedProjection` is
    surjective.
  - The kernel condition holds pointwise: `φ` is injective, and a vector maps
    to zero in the quotient exactly when it lies in `s i.castSucc`.
- `normalizedInductionOutputMatching_of_surjectivity`: assume
  `NormalizedInducedSurjectivity` at `.{uF,uV,uW}` and `.{uF,uW,uW}`. If `σ`
  and `τ` have matching factors and the normalized induction of `σ` has
  finite length, then the two normalized inductions have matching factors.
  1. Source matching provides filtrations `s` of `σ` and `t` of `τ` of the
     same length `m`, a permutation `e`, and equivalences
     `φ i : s.gr i ≃ t.gr (e i)`. The pieces `t.gr j` are smooth: they are
     quotients of subrepresentations of the smooth `τ`
     (`isSmooth_of_injective`, `isSmooth_of_surjective`).
  2. Let `Sσ` and `Sτ` be the value filtrations of the two induced objects
     along `s` and `t`.
  3. For each `i`, `nonempty_valueQuotient_equiv_induced` applies twice: to
     `σ, s, i` with `φ i`, and to `τ, t, e i` with the identity. This gives
     `Sσ.gr i ≃ Ind(t.gr (e i)) ≃ Sτ.gr (e i)`.
  4. `Sσ.gr i` has a composition series because the normalized induction of
     `σ` has finite length (`exists_hasCompositionSeriesLength_graded`). So
     the two graded pieces have matching factors.
  5. The published `gradedJordanHolderRefinement` concludes.
- `normalizedInductionFactorMatchingTheorem_of_smoothInductionSurjectivity`:
  `SmoothInductionSurjectivityStatement.{uF,uV,uW}` and `.{uF,uW,uW}` together
  imply `NormalizedInductionFactorMatchingTheorem.{uF,uV,uW}`. It introduces
  the target's data and applies the two previous results.
- `normalizedInductionFactorMatchingTheorem`: the target. It supplies
  `Induction.smoothInductionSurjectivity` for both hypotheses. Lean infers the
  universe instances `.{uF,uV,uW}` and `.{uF,uW,uW}` of the published proof.

## The second finite-length hypothesis

The target assumes that both normalized inductions have finite length. The
proof uses only the hypothesis for `σ`'s output. The hypothesis for `τ`'s
output is introduced and not used, and the statement keeps it unchanged.

The hypothesis is redundant. By step 3, each graded piece `Sτ.gr (e i)` of
`τ`'s output is equivalent to `Sσ.gr i`, which has a composition series by
step 4. So the graded pieces match in pairs, and `gradedJordanHolderRefinement`
assembles composition series of both outputs. Its conclusion
`HaveSameJordanHolderFactors` includes a composition series of `τ`'s output
with simple factors. That is how `τ`'s output obtains finite length. The proof
does not derive this as a separate lemma.

## Checks

The module compiles in environment 3b864ddf-f0af-4c18-8903-c6f813a0ce0f with
no errors or warnings. `normalizedInductionFactorMatchingTheorem` has universe
parameters `uF uV uW`. It depends only on the axioms `propext`,
`Classical.choice` and `Quot.sound`.

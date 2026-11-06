# Proof: the two dynamic Borels in semisimple rank one

Worker 1301. The theorem `Langlands.GroupScheme.rankOneBorelDynamic` has type
exactly `RankOneBorelDynamicStatement.{u}` from
`Langlands.GroupScheme.Reductive.RankOneBorelDynamicStatement`.

## Statement proved

Let `k : Type u` be an algebraically closed field of arbitrary
characteristic. Let `G` be connected reductive over `k`, and let
`j : T.toGrp ⟶ G` be a maximal torus with `T` split. Assume that no two
actual Lie roots of `j` are linearly independent over `ℤ`. Let `α` be a
root and let `ν` be any cocharacter of `T` with
`latticePairing T α ν ≠ 0`. Then every Borel embedding `b : B ⟶ G` with a
factorization `t ≫ b = j` represents
`Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ j)` or
`Dynamic.parabolic (CommGroupScheme.groupHom (-ν) ≫ j)`. Here
"represents" is the full `SubgroupFunctor.IsRepresentedBy` conclusion:
monomorphism, and equality of subgroup functors on every test scheme.

## Implemented proof

The proof is a single application of the published conditional assembly
`rankOneBorelDynamic_of_projectiveBorelInputs` from
`Reductive.RankOneBorelDynamicAssembly`. It supplies the assembly's four
structural arguments with published theorems, so no hypothesis remains:

- `SolvableProperFixedPointStatement` is `solvableProperFixedPoint`, from
  `SolvableProperFixedPointProof`.
- `ProjectiveTorusFixedPointDimensionStatement` is
  `projectiveTorusFixedPointDimension`, from
  `ProjectiveTorusFixedPointDimension`.
- `SolvableMaximalTorusConjugacyStatement` is
  `solvableMaximalTorusConjugacy_of_torusQuotient solvableTorusQuotient`.
  The first theorem is in `Rational.SolvableMaximalTorusQuotientAssembly`
  and the second in `Absolute.SolvableTorusQuotientProof`.
- `AlgClosedMaximalTorusCentralizerStatement` is
  `algClosedMaximalTorusCentralizer_fromQuotient dynamicCentralizerReductive
  solvableTorusQuotient`. Here `algClosedMaximalTorusCentralizer_fromQuotient`
  is in `Absolute.MaximalTorusCentralizerFromQuotient`; it turns dynamic
  centralizer reductivity and solvable torus quotients into
  self-centralization of maximal tori over an algebraically closed field.
  `dynamicCentralizerReductive` proves `DynamicCentralizerReductiveStatement`
  in `Dynamic.CentralizerReductiveProof`.

## How the assembly proves the statement

The published assembly introduces the statement's data and calls
`prescribedBorelSignedParabolic` on the specified `b`, `t`, `ν` and
factorization. That construction has the following steps.

1. `prescribedBorelDynamicCurveData` builds the proper homogeneous
   quotient of `G` by the prescribed Borel. Its projection is smooth,
   surjective and quasi-compact, with exact coset fibers on every test
   scheme, and the quotient has Krull dimension at most one. The same data
   records that `Z_G(ν ≫ j)` lies in the range of `b`, that the rational span
   of the actual roots has dimension exactly one, and that `b` is not an
   isomorphism. Two parts of this step supply the comparisons the task
   requires:
   - The pairwise-dependence hypothesis gives semisimple rank one through
     the published dependent-root span lemma, applied to the actual nonzero
     root `α`.
   - The original `ν` is made generic on all roots by
     `IsSplitTorus.isRegularCocharacter_of_rankOne`, so `ν` is never
     replaced by a chosen generator.
2. `HomogeneousQuotient.signedParabolicRepresentativeOfCurve` is applied to
   this quotient and Borel. It returns a cocharacter `eta`, a proof that
   `eta = ν` or `eta = -ν`, and a witness that `b` represents the dynamic
   parabolic of `eta ≫ j`. The witness is rewritten along `t ≫ b = j`.

`rankOneBorelDynamic_of_projectiveBorelInputs` then splits `eta = ν` and
`eta = -ν` into the two disjuncts. Each step is described in more detail in
the Markdown of `Reductive.RankOneBorelDynamicAssembly` and
`Reductive.RankOnePrescribedBorelCurve`.

## Provenance and constraints

The target is a derived form of Milne, *Algebraic Groups* (2017),
Lemma 20.20 (printed pp. 414–415), together with Theorem 20.16 and the
discussion after it (printed pp. 412–413). The implemented route
composes named Library results and does not follow Milne's proof line by
line. This module states no new mathematics beyond the composition.

The proof does not use `RegularCocharacterBorelStatement`,
`ParabolicDynamicStatement` or `RankOneSolvableObstructionStatement`. Its
import closure contains no proof of any of them.
`Absolute.BorelStatement` only defines the first two, and
`Absolute.BruhatCoveringSteps` uses the first only as an explicit
hypothesis. The development check reports universe parameter `u` and only
the axioms `propext`, `Classical.choice` and `Quot.sound`.

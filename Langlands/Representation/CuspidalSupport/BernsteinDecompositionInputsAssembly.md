# Assembling the Bernstein decomposition from its named statement inputs

Author: Worker 5313, Task 5313 (`03088b22-a403-46ae-a6ed-6dea22f5472a`).

This module contains derived supporting results for the proof of Renard
VI.7.2 (David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, printed
pp.181–184 / PDF pp.187–190). The source proof of the Theorem uses four
earlier results: the association theorem VI.5.4, the two decompositions
of VI.3.5, and the geometric lemma. The published
`bernsteinCategoryDecomposition_of_representationInputs` has four
hypotheses in its own intermediate forms. This module rewrites three of
them as the published named statements and reduces the fourth, the
geometric exclusion, to supercuspidal inducing objects. The named
statements remain hypotheses here and none of them is proved.

## Declarations

- `bernsteinInducedInertiaJacquetExclusion_of_supercuspidal`: for one
  standard family, `BernsteinInducedInertiaJacquetExclusion.{uF, uV} i ν
  family` follows from two hypotheses. The first is
  `RationalWholeCuspidalCategoryDecompositionStatement.{uF, max uF uV}`
  (VI.3.5, whole-category decomposition). The second, `hsc`, is the
  exclusion `BernsteinJacquetExclusion i ν family a` for the normalized
  induction of `bernsteinLiteralLeviRep i ν a.roots τ`, for every datum
  `a` and every `τ` that lies in the same-Levi inertia block of
  `a.representation` and satisfies `RepresentedParabolic.IsSupercuspidal
  τ`. The proof supplies the extra supercuspidality hypothesis from
  `isSupercuspidal_of_rationalInertiaBlockProperty`
  (module `BernsteinInertiaBlockSupercuspidality`).
- `bernsteinCategoryDecomposition_of_statementInputs`: for one standard
  family, the exact category-decomposition predicate
  `Renard.IsCategoryDecomposition` of the Bernstein blocks follows from
  four hypotheses: represented VI.5.4,
  `RepresentedParabolic.LeviSupercuspidalInductionAssociationStatement.{uF,
  max uF uV}`; VI.3.5, `RationalCuspidalInertiaProductDecompositionStatement.{uF,
  max uF uV}`; VI.3.5, `RationalWholeCuspidalCategoryDecompositionStatement.{uF,
  uV}`; and the family's `BernsteinInducedInertiaJacquetExclusion.{uF, uV}`.
  The proof applies `bernsteinCategoryDecomposition_of_representationInputs`.
  It obtains support uniqueness from the association statement by
  `bernsteinInertialSupportUniqueness_of_represented`, and the finite
  induced-cuspidal embedding from the whole-category statement by
  `rationalCuspidalInducedEmbedding_of_wholeStatement`.
- `bernsteinCategoryDecompositionOfStatementInputs`: the same result as a
  `def` whose type is the implication from the family's
  `BernsteinInducedInertiaJacquetExclusion` to the category decomposition,
  given the three named statements. It is the candidate's entry
  declaration and adds no content.

The field universe `uF` and the carrier universe `uV` are independent. The
local instances give the group and Levi rational points their point
topologies, as in the published Bernstein modules.

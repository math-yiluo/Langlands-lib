# The centralizer Levi of a maximal torus of a parabolic radical

Author: Worker 4388.

`Langlands.GroupScheme.parabolicRadicalTorusCentralizerLevi` proves exactly the
published `Langlands.GroupScheme.ParabolicRadicalTorusCentralizerLeviStatement.{u}`
at arbitrary universe `u`, with no additional premise. The statement pair
`ParabolicRadicalTorusCentralizerLeviStatement` is unchanged.

Fix any field `k`, a connected reductive group scheme `G`, an actual rational
parabolic `j : P → G`, an actual geometric solvable radical `r : R → P`, and an
actual maximal torus `sR : S → R`. The theorem supplies a group scheme `L` and a
morphism `l : L → P` with two properties. First, `l` satisfies the existing
`IsRationalLeviSubgroup` predicate. This includes affineness of `P`, a closed
embedding, connected reductivity of `L`, a represented geometric unipotent
radical, and an isomorphism of schemes given by Levi-first multiplication.
Second, `l ≫ j` represents the whole-torus centralizer of `sR ≫ r ≫ j` in `G`.
This is an equality of subgroup functors on every relative test scheme,
including refinements and nonreduced and nonaffine tests. The proof assumes no
splitness, perfectness, characteristic restriction, ambient maximal torus,
supplied Levi or rational-point density.

## Implemented proof

The proof applies the published conditional theorem
`parabolicRadicalTorusCentralizerLevi_of_dynamic` from
`Rational.ParabolicRadicalTorusInitialLevi`. It supplies that theorem's three
premises with published unconditional proofs:

- `parabolicDynamic` (`Absolute.ParabolicDynamicProof`) proves
  `ParabolicDynamicStatement` (Milne, Theorem 25.1): a closed subgroup of a
  connected reductive group is parabolic exactly when its range is the dynamic
  parabolic of a rational cocharacter.
- `dynamicCentralizerReductive` (`Dynamic.CentralizerReductiveProof`) proves
  `DynamicCentralizerReductiveStatement`: every closed representative of a
  cocharacter centralizer in a connected reductive group is connected
  reductive.
- `solvableMaximalTorusConjugacy` (`Rational.SolvableMaximalTorusConjugacyProof`)
  proves `SolvableMaximalTorusConjugacyStatement`: two maximal tori of a smooth
  connected affine solvable group are conjugate by a rational point, with an
  isomorphism of their sources.

The conditional theorem works in two steps. First,
`parabolicRadicalTorusInitialLevi_of_dynamic` chooses a cocharacter `χ` with
`P = P(χ)`. It takes the represented affine dynamic centralizer `Z(χ)` as the
Levi `L` and the dynamic unipotent subgroup `U(χ)` as its geometric unipotent
radical. Connected reductivity of `Z(χ)` comes from the second premise, and
published dynamic decompositions give the Levi-first multiplication
isomorphism. The image of `χ` is central in `L`. Its split-torus image embeds
in the supplied radical `R` and extends to a maximal torus of `R`. That torus
is central in `L`, so its ambient centralizer equals `Z(χ)` on all tests.
Second, `parabolicRadicalTorusCentralizerLevi_of_initial_torus` uses rational
conjugacy of maximal tori in the smooth connected affine solvable radical to
reach the supplied torus `sR`. It conjugates the initial Levi by the
corresponding rational point of `P`, which preserves the full Levi predicate and
the represented ambient centralizer.

The only axioms used are `propext`, `Classical.choice` and `Quot.sound`.

## Provenance

This module is a formal composition of the named published results. The
original sources and the source rationale are in the statement Markdown
`ParabolicRadicalTorusCentralizerLeviStatement.md`. They are Borel and Tits,
*Groupes réductifs* (1965), Corollary 3.14 and sections 4.1–4.3, 4.15(b) and
4.18, with the 1972 *Compléments* correction 5.5. The implemented route goes
through the dynamic description of parabolics, not through the
internal-centralizer wording of 3.14 and descent. It adds no external
assertion.

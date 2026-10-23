# Fixed-level finiteness of compact-coefficient classes on `G°`

This module proves the published proposition
`Langlands.CuspidalSupport.CompactCoefficientFixedLevelFinitenessTheorem.{uF, uV}`
(module `Langlands.Representation.CuspidalSupport.CompactCoefficientFinitenessStatement`)
as `Langlands.CuspidalSupport.compactCoefficientFixedLevelFiniteness`.
The proposition is Bernstein--Zelevinsky (1976), Theorem 4.14, page 41, in
its compact-open form. It says: for every prime `p`, `p`-adic field `F`,
compatible topological data `T`, positive total rank `n`, block shape `B`,
and compact open subgroup `K` of the determinant-unit subgroup
`G° = determinantUnitSubgroup T B`, the classes in
`CompactCoefficientClass.fixedStratum.{uF, uV} K` form a finite set. These are
the isomorphism classes of irreducible smooth representations with compactly
supported smooth dual coefficients that have a nonzero `K`-fixed vector.

The theorem has no hypotheses beyond those of the published statement.

## Proof

The theorem applies
`compactCoefficientFixedLevelFiniteness_of_cornerStructure` (module
`Langlands.Representation.CuspidalSupport.CompactCoefficientFinitenessReduction`)
to two proved propositions:

- `determinantUnitCornerStructure : DeterminantUnitCornerStructureStatement.{uF}`
  (module `Langlands.Representation.CuspidalSupport.DeterminantUnitCornerStructureProof`):
  the sandwich structure of compact-open Hecke corners of `G°` (BZ76 Lemma 4.9);
- `Langlands.sandwichSimpleModuleDimensionBound`, a proof of
  `SandwichSimpleModuleDimensionBoundStatement.{uH, uM}` used at
  `{uF, uV}` (module `Langlands.Algebra.SandwichDimensionBoundProof`):
  the dimension bound for finite-dimensional simple modules over sandwich
  algebras (BZ76 Lemma 4.10 and §4.11).

The reduction is the argument of BZ76 4.16: a smaller compact open level
`N ≤ K` has a sandwich Hecke corner; the `N`-fixed spaces of the classes in
the `N`-stratum are finite-dimensional simple corner modules of bounded
dimension, pairwise separated by corner elements; finitely generated
representations of bounded dimension with this separation property are
finite in number. Each step is described in the Markdown of its module.

## Supporting modules

- `Langlands.Algebra.SeparatedMatrixRepresentations`: finiteness of separated
  matrix representations of a finitely generated complex algebra.
- `Langlands.Representation.CompactCoefficient.FixedLevelFiniteness`: corner
  modules of fixed vectors, their simplicity, separating corner elements, and
  `fixedStratum_finite_of_sandwich`.
- `Langlands.Representation.CuspidalSupport.CompactCoefficientFinitenessReduction`:
  the reduction to the two propositions above.
- `Langlands.Representation.Hecke.DoubleCosetSandwich`,
  `Langlands.Group.GL.DominantExponentGeneration`,
  `Langlands.Group.GL.PrincipalLevelDominance` and
  `Langlands.Representation.CuspidalSupport.DeterminantUnitCornerStructureProof`:
  the proof of the corner structure.
- `Langlands.Algebra.CommutingDimensionHelpers`,
  `Langlands.Algebra.CommutingDimensionNumerics`,
  `Langlands.Algebra.CommutingDimensionRecurrence`,
  `Langlands.Algebra.CommutingDimensionNilpotent`,
  `Langlands.Algebra.CommutingDimensionPrimary` and
  `Langlands.Algebra.SandwichDimensionBoundProof` (by Worker 307): the
  commuting-endomorphism dimension estimate (BZ76 Lemma 4.10) and the
  dimension bound.

## Checks

A development `lean_check` built all fourteen modules with no errors or
warnings. Inspection of `compactCoefficientFixedLevelFiniteness` reports
universe parameters `uF, uV` and only the axioms `propext`,
`Classical.choice` and `Quot.sound`. This is not independent acceptance.

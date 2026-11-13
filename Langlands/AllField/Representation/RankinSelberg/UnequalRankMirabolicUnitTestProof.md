# All-field port of `Langlands.Representation.RankinSelberg.UnequalRankMirabolicUnitTestProof`

`Langlands.AllField.Representation.RankinSelberg.UnequalRankMirabolicUnitTestProof` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.UnequalRankMirabolicUnitTestProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.UnequalRankMirabolicUnitTestProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Compact mirabolic unit tests for every unequal-rank JPSS block: proof**

One positive principal congruence level `a` is used in both ranks. The larger
test is the coset extension of the standard character from the level-`a`
principal congruence subgroup of the mirabolic group. A Schur-complement
computation shows that the block matrix `diag(g, I) (1 + X)` lies in its
support exactly when `g` lies in `N K(a)` and the rectangular entries lie in
`𝔪^a`. A rescaled actual coefficient function of a vector fixed by `K(a)`
then makes the integrand a constant multiple of the indicator of a compact
open quotient orbit times a compact open rectangle.

## Imports from the port

- `Langlands.AllField.Group.GL.CompactOpen`
- `Langlands.AllField.HarmonicAnalysis.PadicScalarHaarScalingProof`
- `Langlands.AllField.Representation.RankinSelberg.UnequalRankMirabolicUnitTestStatement`

## Declarations

- `Langlands.AllField.RankinSelberg.unequalRankMirabolicUnitTest` (theorem): Every unequal-rank JPSS block admits a compact mirabolic test function and
  an actual smaller coefficient-model vector whose product integral converges and
  equals one for every complex parameter.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.UnequalRankMirabolicUnitTest.levelSet`, `Langlands.RankinSelberg.UnequalRankMirabolicUnitTest.zero_mem_levelSet`, `Langlands.RankinSelberg.UnequalRankMirabolicUnitTest.add_mem_levelSet`, `Langlands.RankinSelberg.UnequalRankMirabolicUnitTest.neg_mem_levelSet`, `Langlands.RankinSelberg.UnequalRankMirabolicUnitTest.mul_mem_levelSet`, `Langlands.RankinSelberg.UnequalRankMirabolicUnitTest.sum_mem_levelSet`, `Langlands.RankinSelberg.UnequalRankMirabolicUnitTest.levelSet_eq_image`, `Langlands.RankinSelberg.UnequalRankMirabolicUnitTest.mem_integer_of_mem_levelSet`, `Langlands.RankinSelberg.UnequalRankMirabolicUnitTest.mem_integer_of_sub_one_mem_levelSet`, `Langlands.RankinSelberg.UnequalRankMirabolicUnitTest.mem_principalLevelSubgroup_iff`, `Langlands.RankinSelberg.UnequalRankMirabolicUnitTest.exists_mem_principalLevelSubgroup`, `Langlands.RankinSelberg.UnequalRankMirabolicUnitTest.sum_dite_lt`, `Langlands.RankinSelberg.UnequalRankMirabolicUnitTest.unequalRankMatrix_apply_top`, `Langlands.RankinSelberg.UnequalRankMirabolicUnitTest.unequalRankMatrix_apply_mid`, `Langlands.RankinSelberg.UnequalRankMirabolicUnitTest.unequalRankMatrix_mem`, `Langlands.RankinSelberg.UnequalRankMirabolicUnitTest.exists_of_unequalRankMatrix_eq`, `Langlands.RankinSelberg.UnequalRankMirabolicUnitTest.isOpen_levelSet`, `Langlands.RankinSelberg.UnequalRankMirabolicUnitTest.isCompact_levelSet`, `Langlands.RankinSelberg.UnequalRankMirabolicUnitTest.entries_eq_pi`, `Langlands.RankinSelberg.UnequalRankMirabolicUnitTest.measurableSet_entries`, `Langlands.RankinSelberg.UnequalRankMirabolicUnitTest.rectangularMeasure_entries`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.

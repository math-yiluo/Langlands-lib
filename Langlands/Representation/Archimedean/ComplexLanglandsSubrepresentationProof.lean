import Langlands.Representation.Archimedean.ComplexJacquetModuleFiniteProof
import Langlands.Representation.Archimedean.ComplexJacquetRankOneProof
import Langlands.Representation.Archimedean.ComplexJacquetFrobeniusProof

/-!
# The subrepresentation form of the Langlands classification for `GL_n(ℂ)`

`complexLanglandsSubrepresentation` proves `ComplexLanglandsSubrepresentationStatement`: every
irreducible admissible `(𝔤𝔩_n(ℂ), U(n))`-module has a nonzero intertwining map into the
`U(n)`-finite functions of the standard module of some list of `n` complex characters whose
exponents have non-decreasing real parts.

The proof composes Library theorems:

* `complexJacquetModuleFinite` (Casselman's theorem: `V/𝔫V` is finite-dimensional and nonzero)
  and `complexJacquetRankOne` (rank-one reordering of Jacquet exponents) give, by
  `complexOrderedJacquetReduction`, a nonzero ordered Jacquet functional;
* `complexJacquetFrobenius` (Frobenius reciprocity) and
  `complexLanglandsSubrepresentationJacquetReduction` turn this functional into the required
  embedding.

See the paired Markdown.
-/

set_option autoImplicit false

namespace Langlands.Archimedean

universe uV

/-- The subrepresentation form of the Langlands classification for irreducible admissible
`(𝔤𝔩_n(ℂ), U(n))`-modules: each embeds, by a nonzero intertwining map, into the `U(n)`-finite
part of a standard module whose characters have exponents with non-decreasing real parts. -/
theorem complexLanglandsSubrepresentation : ComplexLanglandsSubrepresentationStatement.{uV} :=
  complexLanglandsSubrepresentationJacquetReduction complexJacquetFrobenius
    (complexOrderedJacquetReduction complexJacquetModuleFinite complexJacquetRankOne)

end Langlands.Archimedean

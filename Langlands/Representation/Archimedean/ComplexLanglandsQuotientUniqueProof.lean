import Langlands.Representation.Archimedean.ComplexLanglandsSubrepresentationProof
import Langlands.Representation.Archimedean.ComplexStandardJacquetExponentProof
import Langlands.Representation.Archimedean.ComplexStandardHomExponentJacquetReduction
import Langlands.Representation.Archimedean.ComplexStandardHomTransposeProof
import Langlands.Representation.Archimedean.ComplexStandardOppositeOrderHomReduction

/-!
# Uniqueness of Langlands quotients for `GL_n(ℂ)`

`complexLanglandsQuotientUnique` proves `ComplexLanglandsQuotientUniqueStatement`: two
Langlands-ordered lists of `n` complex characters whose standard modules both map nonzero into
the same irreducible admissible `(𝔤𝔩_n(ℂ), U(n))`-module are permutations of each other.

On the way, `complexStandardOppositeOrderHom` proves `ComplexStandardOppositeOrderHomStatement`
(Orth): a nonzero intertwining map from the standard module of a Langlands-ordered list to the
standard module of a list with non-decreasing real exponents exists only between permutations.

Both proofs compose Library theorems:

* Orth from `complexStandardOppositeOrderHomReduction` (E → TP → Orth), with E obtained as
  `complexStandardHomExponentJacquetReduction complexStandardJacquetExponent` and TP as
  `ComplexStandardHomTransposeProof.complexStandardHomTranspose`;
* the target from `complexLanglandsQuotientUniqueReduction` (S1 → Orth → target), with S1 the
  Library theorem `complexLanglandsSubrepresentation`.

See the paired Markdown.
-/

set_option autoImplicit false

namespace Langlands.Archimedean

universe uV

/-- A nonzero intertwining map from the standard module of a Langlands-ordered list `ds` (real
parts of the exponents non-increasing) to the standard module of a list `cs` with
non-decreasing real parts exists only if `ds` is a permutation of `cs`. -/
theorem complexStandardOppositeOrderHom : ComplexStandardOppositeOrderHomStatement :=
  complexStandardOppositeOrderHomReduction
    (complexStandardHomExponentJacquetReduction complexStandardJacquetExponent)
    ComplexStandardHomTransposeProof.complexStandardHomTranspose

/-- **Uniqueness of Langlands quotients for `GL_n(ℂ)`** (Knapp 1994, Theorem 4 (a) and (c)): two
Langlands-ordered lists of `n` complex characters whose standard modules both map nonzero into
the same irreducible admissible `(𝔤𝔩_n(ℂ), U(n))`-module are permutations of each other. -/
theorem complexLanglandsQuotientUnique : ComplexLanglandsQuotientUniqueStatement.{uV} :=
  complexLanglandsQuotientUniqueReduction complexLanglandsSubrepresentation
    complexStandardOppositeOrderHom

end Langlands.Archimedean

import Langlands.Representation.Archimedean.ComplexLargeStandardIrreducibleSplit
import Langlands.Representation.Archimedean.ComplexStandardIrreducibleCriterionReduction
import Langlands.Representation.Archimedean.ComplexStandardUnlinkedSwapReduction
import Langlands.Representation.Archimedean.ComplexGLTwoUnlinkedIrreducibleProof
import Langlands.Representation.Archimedean.ComplexReverseIntertwinerTied
import Langlands.Representation.Archimedean.ComplexTemperedStandardIrreducibleProof

/-!
# The irreducibility criterion for principal series of `GL_n(ℂ)`, "if" direction

`complexStandardIrreducibleCriterion : ComplexStandardIrreducibleCriterionStatement`: for a list
`ds` of `n` complex characters in the Langlands order with no linked pair (Tadić 2009, p. 11 and
Lemmas 3.2–3.3), the `(𝔤𝔩_n(ℂ), U(n))`-module of `U(n)`-finite functions of the standard module
of `ds` is irreducible.

The proof composes proved Library theorems; it does not use Vogan's irreducibility statement
`ComplexLargeStandardIrreducibleStatement`, the non-largeness statement
`ComplexLinkedLanglandsQuotientNotLargeStatement`, or their proofs:

* `complexGLTwoUnlinkedIrreducible` (unlinked principal series of `GL_2(ℂ)` are irreducible) and
  `complexStandardUnlinkedSwapReduction` give `ComplexStandardUnlinkedSwapStatement`: an adjacent
  swap of two unlinked characters is realized by a bijective `(𝔤, K)`-intertwiner;
* `complexTemperedStandardIrreducible` (standard modules with characters of equal real exponent
  part are irreducible) and `complexReverseIntertwinerKernelReduction` give
  `ComplexReverseIntertwinerKernelStatement`: for a Langlands-ordered `ds`, every proper
  `(𝔤, K)`-submodule lies in the kernel of every intertwiner to the standard module of
  `ds.reverse`;
* `complexStandardIrreducibleCriterionReduction` combines the two: reversing an unlinked list by
  adjacent swaps gives an injective intertwiner to the reversed module, whose kernel contains
  every proper submodule, and the standard module is nonzero (`complexStandardNontrivial`).
-/

namespace Langlands.Archimedean

/-- **The irreducibility criterion for principal series of `GL_n(ℂ)`, "if" direction**
(Tadić 2009, p. 11 and Lemmas 3.2–3.3, going back to Želobenko). For a list `ds` of `n` complex
characters in the Langlands order, no two of which are linked, the `(𝔤𝔩_n(ℂ), U(n))`-module of
`U(n)`-finite functions of the standard module of `ds` is irreducible. -/
theorem complexStandardIrreducibleCriterion : ComplexStandardIrreducibleCriterionStatement :=
  complexStandardIrreducibleCriterionReduction
    (complexStandardUnlinkedSwapReduction complexGLTwoUnlinkedIrreducible)
    (complexReverseIntertwinerKernelReduction complexTemperedStandardIrreducible)

end Langlands.Archimedean

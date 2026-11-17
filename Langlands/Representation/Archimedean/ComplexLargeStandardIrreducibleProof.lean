import Langlands.Representation.Archimedean.ComplexTemperedStandardIrreducibleProof
import Langlands.Representation.Archimedean.ComplexLargeStandardIrreducibleSplit
import Langlands.Representation.Archimedean.ComplexStandardIrreducibleCriterionReduction
import Langlands.Representation.Archimedean.ComplexReverseIntertwinerTied
import Langlands.Representation.Archimedean.ComplexLinkedLanglandsQuotientNotLargeProof
import Langlands.Representation.Archimedean.ComplexStandardUnlinkedSwapReduction
import Langlands.Representation.Archimedean.ComplexGLTwoUnlinkedIrreducibleProof

/-!
# Vogan's irreducibility theorem for `GL_n(ℂ)`

`complexLargeStandardIrreducible : ComplexLargeStandardIrreducibleStatement`: for a list of
complex characters in the Langlands order, if the Langlands quotient of the standard module by its
largest proper `(𝔤, K)`-submodule `R` is maximally faithful, then `R = 0`.

The proof composes Library reductions with `complexTemperedStandardIrreducible`:

* `complexGLTwoUnlinkedIrreducible` and `complexStandardUnlinkedSwapReduction` give the unlinked
  swap statement;
* `complexTemperedStandardIrreducible` and `complexReverseIntertwinerKernelReduction` give the
  reverse intertwiner kernel statement;
* `complexStandardIrreducibleCriterionReduction` turns these two into the irreducibility
  criterion;
* `complexLargeStandardIrreducibleSplit` combines the criterion with
  `complexLinkedLanglandsQuotientNotLarge`.
-/

namespace Langlands.Archimedean

/-- **Vogan's irreducibility theorem for `GL_n(ℂ)`** (Vogan 1978, Theorem 6.2, (a) ⇒ (f), in
submodule form). For a list `ds` of `n` complex characters in the Langlands order and the largest
proper `(𝔤, K)`-submodule `R` of the `U(n)`-finite functions of its standard module, if the
Langlands quotient by `R` is maximally faithful then `R = ⊥`. -/
theorem complexLargeStandardIrreducible : ComplexLargeStandardIrreducibleStatement :=
  complexLargeStandardIrreducibleSplit
    (complexStandardIrreducibleCriterionReduction
      (complexStandardUnlinkedSwapReduction complexGLTwoUnlinkedIrreducible)
      (complexReverseIntertwinerKernelReduction complexTemperedStandardIrreducible))
    complexLinkedLanglandsQuotientNotLarge

end Langlands.Archimedean

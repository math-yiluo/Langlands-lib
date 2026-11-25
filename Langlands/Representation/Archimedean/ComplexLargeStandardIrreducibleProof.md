# Proof: Vogan's irreducibility theorem for `GL_n(ℂ)`

Lean module: `Langlands.Representation.Archimedean.ComplexLargeStandardIrreducibleProof`.
Its target is the Library statement `ComplexLargeStandardIrreducibleStatement`.

## Statement proved

`Langlands.Archimedean.complexLargeStandardIrreducible : ComplexLargeStandardIrreducibleStatement`
(Library module `ComplexLargeStandardIrreducibleReduction`). Let `ds` be a list of `n` complex
characters in the Langlands order (`IsComplexLanglandsOrdered ds`). Let `R` be a `(𝔤, K)`-submodule
of the `U(n)`-finite functions of `complexStandardModule n ds` with `R ≠ ⊤` that contains every
proper `(𝔤, K)`-submodule. If the Langlands quotient by `R` is maximally faithful
(`IsMaximallyFaithfulModulo (complexStandardLie n ds) R`), then `R = ⊥`. This is the submodule
form of Vogan 1978, Theorem 6.2, (a) ⇒ (f), for `GL_n(ℂ)`. The Library statement's docstring and
Markdown give the source.

## Proof

The proof is one term that composes Library theorems with `complexTemperedStandardIrreducible`
(module `ComplexTemperedStandardIrreducibleProof`):

1. **Unlinked swaps.** `complexStandardUnlinkedSwapReduction complexGLTwoUnlinkedIrreducible`
   proves `ComplexStandardUnlinkedSwapStatement`: an adjacent swap of two unlinked characters is
   realized by a bijective intertwiner. It reduces to `GL_2(ℂ)`, where unlinked principal series
   are irreducible.
2. **Reverse intertwiner.** `complexReverseIntertwinerKernelReduction
   complexTemperedStandardIrreducible` proves `ComplexReverseIntertwinerKernelStatement`: for
   `ds` in the Langlands order, every proper `(𝔤, K)`-submodule lies in the kernel of every
   intertwiner to the standard module of `ds.reverse`. The Library reduction (module
   `ComplexReverseIntertwinerTied`) needs tempered irreducibility at ties of the Langlands order.
   That input is `complexTemperedStandardIrreducible`.
3. **Irreducibility criterion.** `complexStandardIrreducibleCriterionReduction` turns 1 and 2 into
   `ComplexStandardIrreducibleCriterionStatement`: in the Langlands order, if no two characters
   are linked, the standard module is irreducible. Unlinked swaps produce an injective
   intertwiner to the reversed module, whose kernel contains every proper submodule.
4. **Split.** `complexLargeStandardIrreducibleSplit` combines the criterion with
   `complexLinkedLanglandsQuotientNotLarge` (with a linked pair, the Langlands quotient is not
   maximally faithful) to give `ComplexLargeStandardIrreducibleStatement`. If `ds` is unlinked,
   the module is irreducible, so the proper submodule `R` is `⊥`. Otherwise some pair is linked,
   and `complexLinkedLanglandsQuotientNotLarge` says the quotient by `R` is not maximally
   faithful, contradicting the hypothesis.

Axioms: `propext`, `Classical.choice`, `Quot.sound`.

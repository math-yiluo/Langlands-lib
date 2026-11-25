# Proof of `ComplexLinkedLanglandsQuotientNotLargeStatement`

## Statement proved

`Langlands.Archimedean.complexLinkedLanglandsQuotientNotLarge :
ComplexLinkedLanglandsQuotientNotLargeStatement`. The statement is in the Library module
`ComplexLargeStandardIrreducibleSplit`. Take a Langlands-ordered list `ds` of `n` complex
characters, two of which are linked, and let `R` be the largest proper `(𝔤, K)`-submodule of the
`U(n)`-finite functions of its standard module. Then the Langlands quotient by `R` is not maximally
faithful.

## Proof

The theorem is a term that composes published reductions with published proofs of their inputs.
It introduces no new lemma.

1. `complexStandardUnlinkedSwapReduction complexGLTwoUnlinkedIrreducible :
   ComplexStandardUnlinkedSwapStatement`. Adjacent unlinked characters can be swapped. The input
   is the irreducibility of `GL_2(ℂ)` principal series with unlinked characters.
2. `complexLinkedSmallGrowthReduction`, applied to step 1, gives
   `ComplexLinkedSmallGrowthStatement`. This is the upper growth bound for the dual of a linked
   standard module.
3. `HolomorphicGrowth.complexStandardHolomorphicGrowth : ComplexStandardHolomorphicGrowthStatement`
   is the lower growth bound for the holomorphic factor of `U(𝔤)`.
4. `complexDualSubmoduleAnnihilator_of_growth`, applied to steps 3 and 2, gives
   `ComplexDualSubmoduleAnnihilatorStatement`. The dual contains a small submodule that some
   element of `U(𝔤)` maps to zero, although that element does not act by zero.
5. `complexLinkedLanglandsQuotientNotLarge_of_dualSubmodule`, applied to step 4, gives the
   statement. Through duality and `maximallyFaithfulAnnihilator`, maximal faithfulness modulo `R`
   fails.

## Provenance

This is an internal assembly of results already in the Library. The route is the
dimension-count argument described in the Markdown of the imported modules
(`ComplexLinkedLanglandsQuotientDuality`, `ComplexLinkedLanglandsQuotientGrowth`). It is not the
argument Vogan gives for Theorem 6.2.

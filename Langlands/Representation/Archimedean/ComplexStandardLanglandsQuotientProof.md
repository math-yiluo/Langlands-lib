# Proof of `ComplexStandardLanglandsQuotientStatement`

Lean module: `Langlands.Representation.Archimedean.ComplexStandardLanglandsQuotientProof`.

This module proves
the Library statement `Langlands.Archimedean.ComplexStandardLanglandsQuotientStatement` (module
`Langlands.Representation.Archimedean.ComplexLargeStandardIrreducibleReduction`) as the theorem
`Langlands.Archimedean.complexStandardLanglandsQuotient`. There are no further hypotheses.

## The statement

For every `n` and every list `ds` of `n` complex characters in the Langlands order
(`IsComplexLanglandsOrdered ds`: the real parts of the exponents weakly decrease along the list),
there is a `ℂ`-submodule `R` of the `U(n)`-finite functions of `complexStandardModule n ds` such that:

* `R` is a `(𝔤𝔩_n(ℂ), U(n))`-submodule (`IsGKSubmodule` for `complexStandardRep n ds` and
  `complexStandardLie n ds`);
* `R ≠ ⊤`;
* every proper `(𝔤, K)`-submodule `W` satisfies `W ≤ R`.

So `R` is the largest proper `(𝔤, K)`-submodule. Then the quotient by `R` is irreducible, and it is
the only irreducible quotient: if `M` is a proper submodule with irreducible quotient, then `M ≤ R`,
so `M = R`. This quotient is the Langlands quotient.

The original sources state the theorem in other forms:

* Knapp (1994), Theorem 4 (a) (printed p. 405): if the real parts of the exponents weakly decrease,
  the principal series has a unique irreducible quotient. By the argument above, the Lean
  statement gives this unique irreducible quotient for the `(𝔤, K)`-module of `U(n)`-finite
  functions.
* Badulescu–Renard (2010), Theorem 3.3 (i) (printed pp. 1124–1125): the standard module has a
  unique irreducible quotient, and this quotient occurs with multiplicity one in a Jordan–Hölder
  sequence. So it also uses the finite length of the standard module.

The Lean statement is the largest-proper-submodule form, and that form is what this module proves.
It does not imply finite length, and it does not count how often the Langlands quotient occurs among
composition factors. This module does not prove the finite length of the standard module or the
multiplicity one of the Langlands quotient in a Jordan–Hölder sequence, and its proof does not use
either fact. Cite this theorem for the largest-proper-submodule form only, not for Knapp (1994),
Theorem 4 (a) or Badulescu–Renard (2010), Theorem 3.3 (i) in full.

## Proof

The theorem is a single application of published Library results:

```
complexBlockLanglandsQuotient complexBlockChartIntegrable complexBlockParabolicIntegration
  complexTemperedStandardIrreducible
```

* `complexBlockLanglandsQuotient : ComplexBlockLanglandsQuotientStatement` (module
  `ComplexBlockLanglandsQuotient`) is the implication
  `ComplexBlockChartIntegrableStatement → ComplexBlockParabolicIntegrationStatement →
  ComplexTemperedStandardIrreducibleStatement → ComplexStandardLanglandsQuotientStatement`.
  Its proof cuts a Langlands-ordered list into maximal blocks of exponents with equal real parts.
  The block Jacquet functional `ComplexBlockFunctional.jac` vanishes on every proper
  `(𝔤, K)`-submodule and is nonzero, so the sum of all proper `(𝔤, K)`-submodules is proper. This
  sum is `R`.
* `complexBlockChartIntegrable : ComplexBlockChartIntegrableStatement` (module
  `ComplexBlockChartIntegralProof`): integrability of the block chart integrals, by integrating one
  row at a time.
* `complexBlockParabolicIntegration : ComplexBlockParabolicIntegrationStatement` (module
  `ComplexBlockParabolicIntegrationProof`): the block parabolic integration formula, by induction on
  the block size from the maximal parabolic integration formula.
* `complexTemperedStandardIrreducible : ComplexTemperedStandardIrreducibleStatement` (module
  `ComplexTemperedStandardIrreducibleProof`): complex standard modules whose exponents have equal
  real parts are irreducible. This is used for the tied blocks.

The Lean proof uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## References

* A. I. Badulescu, D. Renard, *Unitary dual of GL(n) at archimedean places and global
  Jacquet-Langlands correspondence*, Compositio Math. 146 (2010), §§2.3–2.4, Definition 3.2 and
  Theorem 3.3 (i), pp. 1122–1125; §9.1, p. 1132 (for `GL_n(ℂ)` the essentially square-integrable
  representations are the characters of `ℂˣ`).
* A. W. Knapp, *Local Langlands correspondence: the archimedean case*, Proc. Sympos. Pure Math. 55,
  Part 2 (1994), §4, (4.1)–(4.3) and Theorem 4 (a), p. 405.

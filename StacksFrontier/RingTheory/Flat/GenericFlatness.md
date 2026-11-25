# Generic freeness over a reduced base

Module `StacksFrontier.RingTheory.Flat.GenericFlatness`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a reduced commutative ring R, a finite type R-algebra S and a finite S-module M, this file finds a dense open of Spec R on which S and M are locally free over R and have the corresponding finite presentations.

The predicate `Algebra.IsFinitePresentationFreeAway R S M f` uses localization at powers of f in R. It requires both S and M after localization to be free over the localized base, the localized algebra to be finitely presented over that base, and the localized module to be finitely presented over the localized algebra. The lemma `Algebra.IsFinitePresentationFreeAway.of_linearEquiv` transports the condition along an S-linear isomorphism.

Under the hypotheses above, `Algebra.dense_iUnion_basicOpen_isFinitePresentationFreeAway` proves density of the union of D(f) over elements satisfying this predicate. The theorem `Algebra.exists_isOpen_dense_isFinitePresentationFreeAway` gives an open dense U such that each point of U lies in a D(f) contained in U with that condition.

The proof inducts on the number of algebra generators, treating S as a module over itself and using cyclic quotients and short exact sequences to recover the module case. It localizes on a dense union of opens where coefficients of relations become units or vanish, using reducedness for the vanishing argument. When a relation has unit leading coefficient after Nagata's change of variables, it makes S finite as a module over a polynomial algebra in fewer variables, where the induction and the module argument apply.

The freeness conclusions over the localized base allow arbitrary rank. The predicate uses fixed localization models, and `Algebra.isFinitePresentationFreeAway_iff` expresses the four conditions in any compatible models.

The open dense statement is Tag 051Z. The density theorem is a special case of EGA IV 11.4.6. The file relates the domain case to Tag 051T. The condition and its locus come from Tag 051U and Tag 051V. The proof uses the methods of Tag 051N, Tag 051W, Tag 051X, Tag 051Y and Tag 00KZ.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [051Z](https://stacks.math.columbia.edu/tag/051Z) | `exists_isOpen_dense_isFinitePresentationFreeAway` | The four conditions on `f` are the condition of Equation 051U, cited as `Algebra.IsFinitePresentationFreeAway`; that definition fixes the models of `R_f`, `S_f` and `M_f`, and `Algebra.isFinitePresentationFreeAway_iff` moves the conclusion to any other models. |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | IV 11.4.6 | `dense_iUnion_basicOpen_isFinitePresentationFreeAway` | special case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Flat/GenericFlatness.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.

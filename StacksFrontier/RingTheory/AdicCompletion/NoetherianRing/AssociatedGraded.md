# Associated graded modules of ideal powers

Module `StacksFrontier.RingTheory.AdicCompletion.NoetherianRing.AssociatedGraded`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a commutative ring S and an ideal J, the file constructs the graded module of the J-adic filtration and equips it with a polynomial action after a finite generating family for J is chosen. This supplies the graded construction used in the Noetherian completion criterion.

`grPiece` is the degree-n quotient Jⁿ/Jⁿ⁺¹, and `grModule` is the direct sum of these pieces. The quotient map `grMk` takes an element of Jⁿ to its class. Multiplication by an element of Jᵈ defines `grShift`, taking the degree-n piece to the degree-(n + d) piece. Since J annihilates each piece by `grPiece_ann`, the scalar action on the pieces and their sum factors through S/J.

Given a generating family a indexed by `Fin t`, `mulA` acts on `grModule` by multiplying by aᵢ and raising degree by one. The explicit module structure `grModulePModule` over `MvPolynomial (Fin t) (S ⧸ J)` makes the variable Xᵢ act by this shift and constants act by S/J-scalars. The library uses this direct sum with a chosen polynomial action as its associated graded object. The lemma `star_pow_eq_span_monomials` identifies Jⁿ with the span of monomials of total degree n in the aᵢ.

The construction assembles commuting shifts into a ring homomorphism to the endomorphisms of the graded module. The span formula follows by induction on n, factoring a degree-(n + 1) monomial into one generator and a degree-n monomial.

The module docstring, headed "Completion for Noetherian rings", presents the whole completion argument: its main results `noetherian_of_isAdicComplete_fg` and `completion_noetherian`, and `grModule_noetherian`, are proved in the modules `CompleteNoetherian` and `GradedNoetherian` of the same directory, not in this file.

## References

The module comments relate this construction to Tag 05GH and cite the completeness input Tag 05GG. For the graded pieces, direct sum, and actions, see EGA 0 10.1.1, EGA 0 15.1.5, EGA 0 16.2.1, EGA 0 19.5.6.2, EGA III 4.3.13, EGA IV 6.10.1, EGA IV 19.6.1, SGA 1 II 4.14, SGA 1 III 6.9, and SGA 7 X 2.14.

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 10.1.1 | `grPiece` | partial |
| EGA | 0 19.5.6.2 | `grPiece` |  |
| SGA | 1 II 4.14 | `grPiece` |  |
| SGA | 1 III 6.9 | `grPiece` |  |
| EGA | 0 10.1.1 | `grModule` | partial |
| EGA | 0 15.1.5 | `grModule` | special case |
| EGA | 0 16.2.1 | `grModule` | special case |
| EGA | III 4.3.13 | `grModule` | partial |
| EGA | IV 19.6.1 | `grModule` | special case |
| EGA | IV 6.10.1 | `grModule` | special case |
| SGA | 1 II 4.14 | `grModule` |  |
| SGA | 7 X 2.14 | `grModule` | special case |
| EGA | IV 6.10.1 | `grPiece_ann` | special case |
| EGA | 0 16.2.1 | `grModuleModuleSJ` | special case |
| EGA | IV 6.10.1 | `grModuleModuleSJ` | special case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/AdicCompletion/NoetherianRing/AssociatedGraded.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 29 declarations of the source file 28 are kept. The 1 left out are not needed by the results for which the extract is made: `mulA_commute`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 15 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.

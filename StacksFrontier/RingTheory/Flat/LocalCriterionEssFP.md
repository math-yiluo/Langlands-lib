# Local flatness for essentially finitely presented maps

Module `StacksFrontier.RingTheory.Flat.LocalCriterionEssFP`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file proves a local flatness criterion for finitely presented modules over an essentially finitely presented local algebra. The base and target rings may be non-Noetherian.

Let R → S be a local homomorphism of commutative local rings, M a finitely presented S-module with compatible R-action, and I a proper ideal of R. If S is essentially finitely presented over R, `Module.Flat.of_rTensor_subtype_injective_of_flat_quotient_of_essentiallyOfFinitePresentation` proves R-flatness of M from flatness of M/IM over R/I and injectivity of I ⊗ᵣ M → R ⊗ᵣ M. The supporting lemmas transport flatness and the two test conditions along compatible ring and module isomorphisms.

The proof writes the rings and module as a filtered colimit of Noetherian local data. It obtains quotient flatness cofinally, uses the tensor injectivity hypothesis to obtain flatness at cofinally many stages, and passes to the colimit. The colimit argument takes place in a common universe. `ULift` gives the statement in independent universes, using finite certificates for tensor vanishing to transport injectivity between the different bases.

The algebra hypothesis uses the library’s `RingHom.EssentiallyOfFinitePresentation`, which presents S as a localization of a finitely presented R-algebra. The hypothesis `hTor` expresses first Tor vanishing through the tensor map on the ideal inclusion. The implementation notes of the module docstring name a transport lemma along a ring isomorphism that is not in the file; flatness is transported by `Stacks.Flatness.EssFPLocalCriterion.flat_of_ringEquiv_of_addEquiv` and `Module.Flat.trans`.

The criterion is Tag 0471. The file cites Tag 00M6 for the tensor form of the Tor condition, Tag 00QM for essential finite presentation, Tag 00QX for the approximation, and Tag 00ML for the Noetherian criterion. Related forms are EGA IV 11.3.12 (b ⇒ a), SGA 1 IV 5.6 ((ii) ⇒ (i)), and SGA 3 VIB 12.7.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [0471](https://stacks.math.columbia.edu/tag/0471) | `of_rTensor_subtype_injective_of_flat_quotient_of_essentiallyOfFinitePresentation` | The hypothesis `Tor_1^R(M, R/I) = 0` is stated in the form Remark 00M6 identifies it with, the injectivity of `I ⊗_R M → R ⊗_R M`, as in the Noetherian sibling 00ML; this is the form the source's proof produces and the form 00ML consumes, and unlike `Tor_1` it puts `R` and `M` in no common universe. Hypothesis (1) is `RingHom.EssentiallyOfFinitePresentation` (Definition 00QM (2)), Mathlib having no such predicate. See the module docstring. |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| SGA | 3 VIB 12.7 | `solution_aux` | Local, special case |
| EGA | IV 11.3.12 | `of_rTensor_subtype_injective_of_flat_quotient_of_essentiallyOfFinitePresentation` | b⇒a, b⇒a for arbitrary A |
| SGA | 1 IV 5.6 | `of_rTensor_subtype_injective_of_flat_quotient_of_essentiallyOfFinitePresentation` | (ii)⇒(i), special case |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Flat/LocalCriterionEssFP.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 7 declarations of the source file 6 are kept. The 1 left out are not needed by the results for which the extract is made: `Stacks.Flatness.EssFPLocalCriterion.flat_of_ringEquiv`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 3 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.

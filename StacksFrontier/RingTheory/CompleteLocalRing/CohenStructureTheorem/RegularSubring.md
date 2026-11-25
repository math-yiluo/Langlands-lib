# Complete local domains finite over regular power series rings

Module `StacksFrontier.RingTheory.CompleteLocalRing.CohenStructureTheorem.RegularSubring`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

A Noetherian local domain R that is complete and separated for its maximal ideal contains a regular complete local subring over which R is module-finite. The subring has the same residue field as R and is a power series ring in finitely many variables.

`IsLocalRing.exists_injective_finite_mvPowerSeries` gives a field or Cohen ring Λ and a finite injective ring map from the power series ring over Λ to R. The source is regular local and complete for its maximal ideal, and its composite with reduction to the residue field of R is surjective.

The proof obtains a coefficient ring Λ by the Cohen structure theorem and substitutes lifts of parameters modulo the extended maximal ideal of Λ, sending the source maximal ideal to an ideal I containing a power of the maximal ideal of R. Finiteness of R/I over the residue field gives module-finiteness by an adic criterion, and dimension comparison gives injectivity and regularity, since a nonzero kernel element would lower the dimension.

The domain hypothesis makes Λ either a field or a Cohen ring. The construction takes d = dim R variables in the field case and d = dim R − 1 in the Cohen ring case, using the dimension drop on quotienting by the uniformizer. The theorem quantifies over Λ in the universe of R and represents the subring as the image of the embedding. Surjectivity of the composite to the residue field identifies its kernel with the source maximal ideal, giving the induced residue field isomorphism.

## References

The main result is Tag 032D. The source cites Tag 0326, Tag 0327, Tag 032A, and Tag 032C for coefficient rings and the Cohen structure theorem, and Tag 0319, Tag 031D, Tag 00OJ, Tag 00KQ, and Tag 00KW for adic and dimension arguments. The table of references below records EGA 0 19.8.8 (ii), EGA 0 16.2.5, EGA 0 16.3.8, EGA IV 21.13.12.1, and EGA IV 6.1.3.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [032D](https://stacks.math.columbia.edu/tag/032D) | `IsLocalRing.exists_injective_finite_mvPowerSeries` | The subring `R₀ ⊆ R` is presented as an injective ring homomorphism `f` from the \   power series ring it is isomorphic to, so that items (1) and (3) are statements about \   `MvPowerSeries (Fin d) Λ` and item (2) is one about `f`: `f.Finite` for finiteness and \   `Function.Surjective ((residue R).comp f)` for the isomorphism on residue fields. \   See the module docstring. |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | IV 21.13.12.1 | `krullDimLE_zero_quotient_of_radical_eq` | partial |
| EGA | IV 6.1.3 | `krullDimLE_zero_quotient_of_radical_eq` | partial |
| EGA | 0 16.2.5 | `exists_systemOfParameters_aux` | partial |
| EGA | 0 16.3.8 | `exists_systemOfParameters_aux` | special case |
| EGA | 0 19.8.8 | `IsLocalRing.exists_injective_finite_mvPowerSeries` | (ii) |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/CompleteLocalRing/CohenStructureTheorem/RegularSubring.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- 5 references to EGA and SGA, written in the source as attributes of that library, are taken out of the Lean text and listed above.

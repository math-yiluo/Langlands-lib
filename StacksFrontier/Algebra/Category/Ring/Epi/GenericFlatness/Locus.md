# The generic freeness locus

Module `StacksFrontier.Algebra.Category.Ring.Epi.GenericFlatness.Locus`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a ring map R → S and an S-module M, call f ∈ R good when `Algebra.IsFinitePresentationFreeAway R S M f` holds: S_f is a finitely presented R_f-algebra, M_f a finitely presented S_f-module, and both are free over R_f (Equation 051U). The file studies the locus U(R → S, M) ⊆ Spec R, the union of the standard opens D(f) over good f (Equation 051V): goodness passes to multiples, the locus behaves well under extensions of modules, and it is local on the base. It is one of four parts of the development of generic flatness; the overview is in `StacksFrontier.Algebra.Category.Ring.Epi.GenericFlatness.Noetherian`.

## Main results

- `Algebra.isFinitePresentationFreeAway_of_finitePresentation_of_free`: if B is finitely presented and free over A and N is finitely presented over B and free over A, every x ∈ A is good.
- `Algebra.IsFinitePresentationFreeAway.of_dvd`: if g is good and g ∣ h, then h is good.
- `Algebra.iUnion_basicOpen_isFinitePresentationFreeAway_inter_subset_of_shortExact` (Tag 051W): for a short exact sequence 0 → M₁ → M₂ → M₃ → 0 of S-modules, U(M₁) ∩ U(M₃) ⊆ U(M₂).
- `Algebra.image_comap_iUnion_basicOpen_isFinitePresentationFreeAway` (Tag 051X): for f ∈ R and arbitrary models R_f, S_f, M_f of the localizations, the image of U(R_f → S_f, M_f) under Spec R_f → Spec R is D(f) ∩ U(R → S, M).

## Proofs

Extensions: localizing is a flat base change, so M₂,f is an extension of M₃,f by M₁,f, and finite presentation and freeness pass to extensions; the good element for M₂ is f₁f₃. Locality: an element g = b/fⁿ of R_f is good exactly when fb is good for R → S, M.

## Watch for

- The locus U(R → S, M) has no definition of its own; each statement writes it out as a union of standard opens.
- The module docstring also announces the density statement of Tag 051Y, which the file does not contain.

## References

Tags 051W and 051X, Equations 051U and 051V, and the section Tag 051Q.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [051W](https://stacks.math.columbia.edu/tag/051W) | `iUnion_basicOpen_isFinitePresentationFreeAway_inter_subset_of_shortExact` | The locus `U(R → S, M)` of Equation 051V, which has no separate definition here, is written out as the union of the standard opens `D(f)` over the `f` satisfying Equation 051U, i.e. over `Algebra.IsFinitePresentationFreeAway R S M f`. See the module docstring. |
| [051X](https://stacks.math.columbia.edu/tag/051X) | `image_comap_iUnion_basicOpen_isFinitePresentationFreeAway` | The locus `U(R → S, M)` of Equation 051V is written out as the union of the standard opens `D(g)` over the `g` satisfying 051U, cited as `Algebra.IsFinitePresentationFreeAway`; the identification `Spec(R_f) = D(f)` is the open embedding `PrimeSpectrum.comap (algebraMap R R_f)`, along which the left-hand side is pushed forward. See the module docstring. |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/Algebra/Category/Ring/Epi/GenericFlatness/Locus.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 14 declarations of the source file 12 are kept. The 2 left out are not needed by the results for which the extract is made: `Algebra.dense_iUnion_basicOpen_isFinitePresentationFreeAway_of_localizationAway`, `basicOpen_subset_closure_iUnion_basicOpen_isFinitePresentationFreeAway`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.

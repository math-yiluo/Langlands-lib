# The total ring of fractions of a reduced tensor product

Module `StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.StalkBaseChange`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Write K for the total fraction ring of A, B for a flat A-algebra, and L for B localized at the image of the non-zero-divisors of A, with L finite over K. Let O be an A-algebra that is a domain, with Artinian fraction ring F and compatible scalar towers.

`isArtinianRing_fractionRing_nilradicalQuotient_tensorProduct` proves that the total fraction ring of the reduction of O ⊗[A] B is Artinian. It identifies that ring with the reduction of F ⊗[K] L, a finite algebra over F. This result uses flatness of B and finiteness of L over K; finiteness of B over A is not among its hypotheses.

The module docstring describes the local rings of the normalization of a finite flat base change, the identification used in the reduced fibre theorem. The two results it lists for that are not in the file, and the namespace block meant for them is empty.

The module docstring cites Stacks Project, Tag 0C3B and Tag 09IL.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/AlgebraicGeometry/Morphisms/Normalization/StalkBaseChange.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 3 declarations of the source file 1 are kept. The 2 left out are not needed by the results for which the extract is made: `AlgebraicGeometry.Scheme.exists_ringEquiv_stalk_normalizationScheme_localizationAtPrime_of_tensorProduct`, `AlgebraicGeometry.Scheme.exists_ringEquiv_stalk_normalizationScheme_pullback_localizationAtPrime`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).

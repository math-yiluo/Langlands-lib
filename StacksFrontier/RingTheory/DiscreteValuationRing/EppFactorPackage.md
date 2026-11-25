# Integral closures of individual field factors

Module `StacksFrontier.RingTheory.DiscreteValuationRing.EppFactorPackage`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a field factor E of a reduced tensor base change, this file provides the maps and DVR structure on the integral closure S of B in E, used to formulate weak-solution data at that factor.

- `integralClosureFactorMap` takes the integral closure of A in K₁ to S by mapping its elements from K₁ into E. It uses a compatible square A → B → E and A → K₁ → E. More generally, `integralClosureBaseMap` and `algebraIntegralClosureBase` give the map and algebra structure for any A-integral ring R with compatible maps A → R → E.
- `algebraMap_factor_eq` gives the commuting square A → B → E, A → K₁ → E, and `algebraMap_integralClosureBase_eq` the square A → B → S, A → R → S for the abstract base. `algebraMap_integralClosure_factor_eq_of_tower` identifies the composites B → L → E and B → S → E when B → L → E is a scalar tower.
- `isDiscreteValuationRing_integralClosure_factor` gives the DVR property of S for a henselian DVR B and a finite extension E of its fraction field L. Related lemmas supply E as the fraction field and locality of the structure map from B.
- `isExtension_base_integralClosure_factor` gives a DVR extension R → S when A → R and A → B are DVR extensions, R is integral over A and acts faithfully on E, and the henselian, finite-extension and tower hypotheses hold.

The commuting square transports integral equations from A to B, so the field map restricts to integral closures. For locality in a compatible tower A → R → S, a uniformizer of A is a unit times a power of a uniformizer of R. Locality of A → S forces the latter uniformizer to map into the maximal ideal of S.

The algebra structure `algebraIntegralClosureBase` is introduced locally with `letI`, since its construction uses A. The file supplies the factor DVRs and their maps. The assembly still requires weak solutions for every factor over the prescribed common extension. The docstrings name as consumer a combiner in `EppDegreePrimeBridge` that the module does not contain, and list a faithfulness lemma for B → S and a factor-map square that this file does not contain.

References include Tag 09EM and Tag 09EN. The discussion of the all-factor requirement refers to clause (3) of Tag 09ET.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/EppFactorPackage.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 22 declarations of the source file 19 are kept. The 3 left out are not needed by the results for which the extract is made: `Stacks.EppTheorem.algebraIntegralClosureFactor`, `Stacks.EppTheorem.algebraMap_integralClosureFactor_eq`, `Stacks.EppTheorem.faithfulSMul_integralClosure_factor`.
- 3 commands that are not declarations are left out or changed with the declarations left out (`notes/reuse/stacks-extract/extract-commands.tsv.md`).
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).

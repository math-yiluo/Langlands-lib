# Purely inseparable steps and reduced base change

Module `StacksFrontier.RingTheory.DiscreteValuationRing.EppAlgClosedResidue.PurelyInseparableCase`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file constructs weak solutions for purely inseparable prime-degree steps in a discrete valuation ring tower. It also shows how to test weak solutions on another presentation of the reduced compositum and on the factors of a reduced tensor product.

## Results

- `exists_finite_extension_isWeakSolution_of_isPurelyInseparable` gives a finite extension of K that is a weak solution for A → C in a compatible DVR tower A → B → C with fraction fields K → L → M. The rings A and B are maximal-ideal-adically complete, A → B is weakly unramified, and M/L is purely inseparable of prime degree p.
- `isWeakSolution_iff_of_reducedCompositum_equiv` tests a weak solution using another presentation F of the reduced compositum. The equivalence must respect the L- and K₁-actions. The test is ramification index one at every maximal ideal of the integral closure of B in F, over the integral closure of A in K₁.
- `isWeakSolution_of_iterated_factors` takes a compatible finite product decomposition after the first base change and presentations of the reduced base changes of all its factors. If the corresponding integral closures have ramification index one at every maximal ideal, the composite extension is a weak solution. `isWeakSolution_integral_base_change` transports the index-one condition to closures over compatible smaller rings when the larger rings are integral over them.

The prime-degree proof uses a trichotomy. The identity extension suffices when A → C is already weakly unramified. If C contains a p-th root of a base uniformizer, adjoining that root to K gives a reduced compositum isomorphic to M and the tower formula forces the index of the resulting DVR extension to be one. The third case uses a finite totally ramified separable base change. The product argument uses tensor associativity and reduction modulo the nilradical in each factor.

The purely inseparable theorem uses one universe for all the rings and fields and derives characteristic p from the degree hypothesis. The module docstring announces a totally ramified case; the file has no separate result for it.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/EppAlgClosedResidue/PurelyInseparableCase.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 30 declarations of the source file 29 are kept. The 1 left out are not needed by the results for which the extract is made: `IsDiscreteValuationRing.exists_isWeakSolution_of_isWeaklyUnramified_of_totallyRamified`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.

# Abhyankar’s lemma for extensions of discrete valuation rings

Module `StacksFrontier.RingTheory.DiscreteValuationRing.Abhyankar.AbhyankarLemma`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Abhyankar’s lemma gives a sufficient condition for formal smoothness of the local maps between normalizations after a finite extension of the base fraction field.

`IsDiscreteValuationRing.formallySmooth_localizations_of_ramificationIndex_dvd` starts with an injective local extension A → B of discrete valuation rings with fraction fields K and L, and a finite field extension K₁/K. It decomposes the reduction of the tensor product of L and K₁ over K as a nonempty finite product of fields Eᵢ that are finite over L. In each factor it constructs the compatible map from A₁, the integral closure of A in K₁, to B₁, the integral closure of B in Eᵢ. For maximal ideals q of B₁ over p of A₁, if the ramification index of B over A divides that of p over A, then the induced map of localizations is an injective local map of discrete valuation rings and is formally smooth for the target maximal-ideal adic topology.

When the initial ramification index is one, the proof transfers formal smoothness to the tensor field factors. For larger index it passes to an auxiliary extension with étale normalization over the local base and an e-th root of π, applies the uniformizer-power smoothness result, and descends adic formal smoothness. Private lemmas supply scalar towers, faithfulness after localization at a prime, and injectivity of a map between integral closures compatible with the inclusions into the fields.

The hypothesis `htame` is either residue characteristic zero or coprimality with the initial index together with `Algebra.StacksIsSeparableExtension` on residue fields. `Algebra.StacksIsSeparableExtension` is the library’s own notion, defined for field extensions that need not be algebraic: every finitely generated intermediate field is separably generated. The field factors Eᵢ live in the maximum universe of A, B, K, L and K₁. The module docstring also announces a Kummer-overfield property for tame ramification, with first lemmas towards it; the file contains neither.

Stacks Project, Tag 0BRM and Tag 09EV.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [0BRM](https://stacks.math.columbia.edu/tag/0BRM) | `formallySmooth_localizations_of_ramificationIndex_dvd` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/Abhyankar/AbhyankarLemma.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 15 declarations of the source file 5 are kept. The 10 left out are not needed by the results for which the extract is made: `IsDiscreteValuationRing.HasUnramifiedKummerOverfield`, `IsDiscreteValuationRing.exists_algEquiv_of_surjective_pi`, `IsDiscreteValuationRing.exists_large_unit_multiple`, `IsDiscreteValuationRing.exists_separable_tensor_factor`, `IsDiscreteValuationRing.isLocalization_integralClosure`, `IsDiscreteValuationRing.isSeparableExtension_of_isSeparable`, `IsDiscreteValuationRing.isSeparable_of_isSeparableExtension`, `IsDiscreteValuationRing.isSeparable_of_isSeparablyGenerated`, `IsDiscreteValuationRing.ramificationIdx_atPrime`, `IsDiscreteValuationRing.unram_transport`.
- 1 command that is not a declaration is left out or changed with the declarations left out (`notes/reuse/stacks-extract/extract-commands.tsv.md`).
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).

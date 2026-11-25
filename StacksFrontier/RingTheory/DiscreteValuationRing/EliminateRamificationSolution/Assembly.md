# Elimination of ramification from Epp's theorem: final assembly

Module `StacksFrontier.RingTheory.DiscreteValuationRing.EliminateRamificationSolution.Assembly`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This is the last part (part 7) of the library's derivation of elimination of ramification (Tag 09II) from Epp's theorem (Tag 09F9). For an extension A → B of discrete valuation rings with fraction fields K ⊆ L, B essentially of finite type over A, it produces a finite extension K₁/K that is a solution for A → B, in the sense of the library's `IntegralClosureBaseChange.IsSolution`, assuming Epp's theorem.

## Main result

`exists_finite_extension_isSolution_of_eppTheorem`: under the hypotheses above, given `EppTheorem` at the universes of (A, B, K, L) and again at the universes (uK, max uL uK, uK, max uL uK), there are a finite extension K₁/K and an `IntegralClosureBaseChange` for A → B over K₁ that is a solution.

## Proof

- Residue characteristic zero: `exists_finite_extension_isSolution_of_charZero`. Perfect residue field of A: `exists_finite_extension_isSolution_of_perfectField`. Both are proved in other parts of the development.
- Otherwise: `exists_algebraic_extension_isDiscreteValuationRing_integralClosure` gives an algebraic E/K over which the integral closure A' of A is a discrete valuation ring with perfect residue field. By `integralClosure_reducedTensorProduct_isNoetherian_and_spec_surjective`, the integral closure C of B in (L ⊗_K E)_red is Noetherian; being integral over B, it then has finite spectrum, and its localizations at maximal ideals are discrete valuation rings over A'. Epp's theorem at the second universe profile, through `exists_finite_extension_localSolutions_of_perfectField`, gives a finite E₀/E solving all these local problems. A further finite extension E₁ makes the reduced tensor product geometrically reduced, `exists_isSolution_of_tower` transports the local solutions to E₁, and the local homomorphisms at maximal ideals become adically formally smooth.
- A private step, `exists_finite_extension_isSolution_of_formallySmooth_algebraicExtension`, descends to a finite subextension: given an algebraic E/K with Dedekind integral closure of A, Noetherian integral closure C of B in (L ⊗_K E)_red, a map from the integral closure of A in E to C compatible with E → (L ⊗_K E)_red, geometric reducedness over E, and `RingHom.FormallySmoothNAdic` for the localizations of that map at every maximal ideal of C, there is a finite intermediate field F at which prime spectra are already in bijection, C is generated, and the nilradical is defined. Then C is the base change of the integral closure at stage F, and formal smoothness descends, giving a solution over F.

## Points to watch

- The main theorem is conditional: Epp's theorem enters as the hypotheses `hEpp` and `hEppLocal`, at two universe profiles. It carries no tag in this file.
- K₁ lies in the universe of K, and the solution predicate carries an extra free universe parameter.
- `IsSolution`, `IntegralClosureBaseChange` and `RingHom.FormallySmoothNAdic` are the library's own notions, not Mathlib's.

## References

Tag 09II, Tag 09F9.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/EliminateRamificationSolution/Assembly.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).

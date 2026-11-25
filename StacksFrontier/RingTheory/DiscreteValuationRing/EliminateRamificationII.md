# Integral closures after an algebraic base extension

Module `StacksFrontier.RingTheory.DiscreteValuationRing.EliminateRamificationII`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Let A → B be an extension of discrete valuation rings with fraction fields K → L, with B essentially of finite type over A. For an algebraic extension K'/K, possibly infinite, let A' be the integral closure of A in K', L' = (L ⊗_K K')_red, and B' the integral closure of B in L'. The file shows that B' is Noetherian when A' is, that Spec B' → Spec A' is surjective, and that the residue field extensions are essentially of finite type.

## Main results

- `integralClosure_reducedTensorProduct_isNoetherian_and_spec_surjective` (Tag 09IH): under the hypotheses above (A → B injective and local, B essentially of finite type over A, K'/K algebraic, A' Noetherian), B' is Noetherian, and there is a ring homomorphism f : A' → B', characterized by its composite with the inclusion into L', such that Spec B' → Spec A' is surjective and, for every prime q of B', the map of residue fields κ(f⁻¹q) → κ(q) is essentially of finite type.
- `reducedTensorProduct_isArtinian`: if L is essentially of finite type over K and K'/K is algebraic, (L ⊗_K K')_red is Artinian.

## Proofs

The reduced tensor product is Artinian and reduced, hence a finite product of fields, and in each factor the image of B ⊗_A A' has that field as fraction field. That image is Noetherian of dimension at most one, so `IsIntegralClosure.isDedekindDomain_and_comap_surjective_and_quasiFinite` applies factor by factor, and integral closure commutes with finite products (`integralClosurePiEquiv`). Surjectivity on spectra combines the faithfully flat base change Spec(B ⊗_A A') → Spec A' with the integral map B ⊗_A A' → B', whose kernel is nil. Quasi-finiteness of B' over B ⊗_A A' gives the residue field statement.

## Points to watch

- Finite generation of residue field extensions is stated as `RingHom.EssFiniteType`, not `RingHom.FiniteType`; the module docstring notes that a rational function field is finitely generated as a field but not as an algebra, citing a lemma `ratFunc_not_finiteType` that is not in the file.
- Noetherianity of A' is a hypothesis, not proved.
- The reduction is the quotient by the nilradical, and the map A' → B' is supplied in the statement because no algebra instance between the two integral closures is inferred.

## References

Tag 09IH.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [09IH](https://stacks.math.columbia.edu/tag/09IH) | `integralClosure_reducedTensorProduct_isNoetherian_and_spec_surjective` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/EliminateRamificationII.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 25 declarations of the source file 22 are kept. The 3 left out are not needed by the results for which the extract is made: `IsDiscreteValuationRing.ratFunc_not_finiteType`, `IsDiscreteValuationRing.rightMap`, `IsDiscreteValuationRing.rightMap_apply`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).

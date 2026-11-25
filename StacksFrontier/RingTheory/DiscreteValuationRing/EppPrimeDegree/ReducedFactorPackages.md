# Presentations on matching reduced tensor factors

Module `StacksFrontier.RingTheory.DiscreteValuationRing.EppPrimeDegree.ReducedFactorPackages`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

This file transports weak unramifiedness and extension presentations to the field factors of reduced tensor products. It also solves a single equal-characteristic factor when the Laurent coefficient roots have already been supplied by the base.

`isWeaklyUnramified_integralClosure_factor_of_perfectResidue` takes a weakly unramified extension A → B of complete DVRs with perfect base residue field and a henselian instance on B. Given finite K₁/K, an integral DVR model R of K₁ over A, and a decomposition of the reduced L ⊗[K] K₁ compatible with both tensor maps, it proves that the integral closure of B in each field factor is weakly unramified over R. The proof uses the factor criterion for a canonical weak solution and identifies R with the integral closure of A in K₁.

For matching lower and upper factors E and F, the next two results use a surjective upper tensor map `phi` with the prescribed action on pure tensors.

- `artinSchreierFactorPackage_of_matching_reducedFactors` takes a characteristic-p Artin–Schreier presentation of M/L with prime p. The mapped generator presents F/E, which is either degree one with surjective structure map or Galois of degree p.
- `cyclotomicFiniteLevelFactorPackage_of_matching_reducedFactors` takes a characteristic-zero cyclotomic finite-level presentation of M/L and a compatible local map B → S of DVRs with residue characteristic p on S. It gives the same degree alternatives and retains the mapped finite-level datum in the degree-p case.

`exists_finite_extension_isWeakSolution_of_reentered_constant_laurent` gives a finite weak solution for R → T in a tower R → S → T with fraction fields K → E → F. It requires K of characteristic p, F/E finite, complete R and S, perfect residue field for R, and weakly unramified A → R and R → S. It takes a Laurent presentation from B, with compatible residue lifts and truncation, and an Artin–Schreier generator over E. The hypothesis `hrootBase` supplies matching images of the prescribed coefficient roots in the residue field of S.

Surjectivity on upper factors gives surjectivity from E ⊗[L] M, so mapping the original generator preserves generation. The constant Laurent proof transports the truncated coefficient data and applies the family solver to a singleton. The statements use one universe.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/EppPrimeDegree/ReducedFactorPackages.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 7 declarations of the source file 6 are kept. The 1 left out are not needed by the results for which the extract is made: `Stacks.EppTheorem.cyclotomicPresentation_of_matching_reducedFactors`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).

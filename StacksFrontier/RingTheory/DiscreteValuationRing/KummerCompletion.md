# Completion of the integral closure in a uniformizer root extension

Module `StacksFrontier.RingTheory.DiscreteValuationRing.KummerCompletion`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Let A be a discrete valuation ring with fraction field K and uniformizer π. For n ≥ 2, let Aₙ be the integral closure of A in K(π^(1/n)). The file relates the maximal-ideal completion of Aₙ to the same root construction over the completion Â of A.

`exists_ringEquiv_adicCompletion_A1` gives a ring equivalence from the completion of Aₙ to the integral closure of Â in K̂(π̂^(1/n)), where K̂ is the specified fraction field of Â and π̂ is the image of π. On elements of A the equivalence agrees with the structural map through Â. `finite_A1` shows that Aₙ is module-finite for n ≥ 2 and a uniformizer π. `isIntegral_A1` supplies integrality, and `isFractionRing_A1` gives K(π^(1/n)) as the fraction field of Aₙ with an irreducibility instance for Xⁿ − π over K.

The proof uses finite base change for completion, writes Aₙ as the quotient adjoining a root, and uses `AdjoinRoot.baseChangeAlgEquiv` to move that quotient over Â. The canonical integral-closure equivalence over Â gives the final identification.

The main theorem assumes that Â is a domain and a discrete valuation ring and that π̂ is a uniformizer (`hπh`). It also takes irreducibility over K and localness of Aₙ as instances. The conclusion is existential and records compatibility on the image of A.

The references are Tag 09EV for the root construction, Tag 07N9 for finite base change, and Tag 09F9 and Tag 09EJ for the surrounding completion arguments.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/DiscreteValuationRing/KummerCompletion.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).

# Integral closure after tensor base change

Module `StacksFrontier.RingTheory.TensorProduct.ReducedFractionRingIntegralClosure`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file compares integral closures using the total ring of fractions of a reduced tensor product. Set P = `O ⊗[A] B` and let D be the reduction of `F ⊗[K] L`.

For the specified scalar towers, `isScalarTower_tensorProductFractionRing` factors the structure map from O to the latter tensor product through P. If B is finite over A, `integralClosureTensorProductAlgebra` equips the integral closure of O in D with a P-algebra structure.

`nonempty_algEquiv_integralClosure_fractionRing_tensorProduct` gives an isomorphism over P from the integral closure of P in the total ring of fractions of its reduction to the integral closure of O in D. It assumes O is a domain, F is its Artinian total fraction ring, K is the total fraction ring of A, B is finite flat over A, and L is the localization of B at the nonzerodivisors of A and is finite over K.

The proof identifies the ambient fraction rings and uses integrality of P over O to compare integral elements. A may be any commutative ring.

Tag 09IL.

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/TensorProduct/ReducedFractionRingIntegralClosure.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).

# Finite support for integral relative ideles

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Adele.IntegralTensorSupport.IdeleSupport`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be a finite extension of number fields. For a relative idele z (`RelativeIdeleGroup K L`), this file gives one finite set of finite places of K outside which the finite component of z is an integral unit in every factor of the local tensor decomposition.

- `relativeIdeleLocalTensorDecompositionSupport z`: the union of the coefficient support `relativeIdeleCoefficientSupport z` and the finite set `integralTensorBadPlaces`, which does not depend on z. `mem_relativeIdeleLocalTensorDecompositionSupport_iff` describes membership.
- `relativeIdele_finiteComponent_localTensorDecompositionIntegralUnit_of_notMem`: if w lies outside this set, the component of z at w satisfies `RelativeLocalTensorDecompositionIntegralUnitAt`. So it and its inverse lie in the valuation ring of every completion factor above w.

The proof combines two imported results. Outside the coefficient support, the basis coordinates of z and z⁻¹ are integral. Outside the bad places, such basis integrality implies integrality in the local tensor decomposition.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Adele/IntegralTensorSupport/IdeleSupport.lean`: the Lean file is the source byte for byte (SHA-256 `a8a982086c6810d0310cde6cf8119914de089d6cf22bc163a6778206ddef3209`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.

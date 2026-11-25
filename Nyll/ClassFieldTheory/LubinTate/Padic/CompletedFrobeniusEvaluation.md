# Semilinear evaluation for the completed Frobenius lifts

Module `Nyll.ClassFieldTheory.LubinTate.Padic.CompletedFrobeniusEvaluation`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let A be the completed maximal unramified extension of ℚ_p with arithmetic Frobenius φ, W its Witt ring of integers, and E the completed Lubin–Tate level at level n. For a unit u of ℤ_p, the completed Frobenius lift σ_u is a field automorphism of E acting on A by φ. The file shows that σ_u preserves the valuation ring of E, is continuous for its adic topology, and transforms convergent evaluation of power series over W semilinearly; it then computes σ_u on the multiplicative primitive point.

## Main definitions and results

- `padicCompletedUnramifiedFrobeniusIntegerEquiv`: φ restricted to the valuation ring of A, with simp lemmas for it and its inverse; `padicCompletedUnitFrobeniusLiftEquiv_symm_algebraMap`: σ_u⁻¹ acts on A by φ⁻¹.
- `padicCompletedUnitFrobeniusLiftEquiv_mem_valuationSubring`, `..._symm_mem_valuationSubring`, `..._mem_valuationSubring_iff`: σ_u and its inverse preserve the valuation ring of E.
- `padicCompletedUnitFrobeniusIntegerEquiv p n u`: the induced ring automorphism r_u of the valuation ring, with coercion lemmas.
- `padicCompletedUnitFrobeniusIntegerEquiv_continuous`: r_u is continuous for the maximal-ideal adic topology.
- `padicCompletedUnitFrobeniusIntegerEquiv_wittCoefficientHom`: on images of W, r_u acts by Witt-vector Frobenius.
- `padicCompletedUnitFrobeniusIntegerEquiv_hasEval`: r_u preserves admissible evaluation points.
- `padicCompletedUnitFrobeniusIntegerEquiv_evaluation`: r_u(f(x)) = φ(f)(r_u(x)) for every power series f over W and admissible x, φ(f) acting on coefficients.
- `padicCompletedUnitFrobeniusIntegerEquiv_primitiveRoot`: r_u sends the standard primitive point to its standard unit translate.
- `padicCompletedUnitFrobeniusIntegerEquiv_multiplicativePrimitivePoint`: r_u sends the multiplicative primitive point to its multiplicative unit translate.

## Proofs

Preservation of the valuation ring: it is the integral closure of the valuation ring of A, and σ_u is compatible with φ on that base, so it preserves integrality. Continuity holds because r_u preserves every power of the maximal ideal. Semilinearity follows by mapping the convergent sum defining f(x) through the continuous r_u and using uniqueness of limits. For the multiplicative point, which is the standard-to-multiplicative intertwiner H evaluated at the standard primitive point, semilinearity, φ(H) = H and the intertwining of H with scalar endomorphisms give the result.

## Watch for

- The evaluation uses local instances from an imported file: a uniform structure on W and the maximal-ideal adic topology on the valuation ring of E, with its completeness and Hausdorff property.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LubinTate/Padic/CompletedFrobeniusEvaluation.lean`: the Lean file is the source byte for byte (SHA-256 `8d06d9d5dbba0cbc33e7b36ab6a2215677065e523631e9fe03a789f8246a7897`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.

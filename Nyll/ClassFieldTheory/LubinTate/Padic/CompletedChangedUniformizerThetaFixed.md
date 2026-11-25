# The changed theta value is fixed by the diagonal Frobenius

Module `Nyll.ClassFieldTheory.LubinTate.Padic.CompletedChangedUniformizerThetaFixed`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let E be the completed p-adic Lubin–Tate level at level n, x its multiplicative primitive point, u a unit of ℤ_p, and H the changed-uniformizer intertwiner. The changed theta value θ is H evaluated at x (`padicChangedUniformizerThetaValue`). The file shows that the completed Frobenius lift indexed by u⁻¹, which acts on coefficients by Witt-vector Frobenius and sends x to [u⁻¹]x, fixes θ.

## Main results

- `padicCompletedDiagonalFrobenius_multiplicativeUnitAction`: if r is the Frobenius lift indexed by u⁻¹ on the valuation ring of E, then [u](r(x)) = x, where [u] is the multiplicative scalar endomorphism of u evaluated at a point.
- `padicCompletedChangedUniformizerThetaValue_fixed_by_diagonalFrobeniusInteger`: r(θ) = θ in the valuation ring of E.
- `padicCompletedChangedUniformizerThetaValue_fixed_by_diagonalFrobenius`: the same for the field automorphism `padicCompletedUnitFrobeniusLiftEquiv p n u⁻¹`.

## Proofs

Semilinearity of r on evaluations gives r(H(x)) = φ(H)(r(x)), with φ(H) the series with Witt-vector Frobenius applied to its coefficients. The identity φ(H) = H ∘ [u] from the scalar-compatibility file turns this into H([u](r(x))), and [u](r(x)) = x because r(x) = [u⁻¹]x and the unit actions cancel. Hence r(θ) = H(x) = θ.

## Watch for

- The evaluation of power series in the valuation ring of E is set up with private local instances: the discrete uniformity on the Witt ring, and the adic topology of the maximal ideal on the valuation ring of E, which is complete and Hausdorff.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LubinTate/Padic/CompletedChangedUniformizerThetaFixed.lean`: the Lean file is the source byte for byte (SHA-256 `f879a4c7ea813a8aa8e60c1fb663bbab9951d3ad94ca54ab351cf965f3a6929f`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.

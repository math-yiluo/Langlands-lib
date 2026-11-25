# Recursive coefficients for Lubin–Tate intertwiners

Module `Nyll.ClassFieldTheory.LubinTate.FormalModule.RecursiveCoefficient`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let π be a uniformizer of a local field K, e and ē Lubin–Tate series for π, and H a power series in finitely many variables with prescribed linear term. Every coefficient of the intertwining defect e(H) − H(ē(Xᵢ)ᵢ) is divisible by π (proved in the reduction file). The file divides out π and selects the coefficient that cancels the defect at a multi-degree d of total degree at least 2.

## Main definitions

In `LubinTate.SameUniformizer`:

- `normalizedDefectCoefficient hπ e ebar hH d`: an element δ with π·δ equal to the degree-d defect coefficient, chosen by `Classical.choose`.
- `correctionCoefficient hπ e ebar hH d hd`: for |d| ≥ 2, the unique c with (1 − π^(|d|−1))·c = −δ.

## Main results

- `uniformizer_mul_normalizedDefectCoefficient`: π·δ is the degree-d defect coefficient.
- `correctionCoefficient_spec`: c satisfies its defining equation.
- `correctionCoefficient_unique`: any c satisfying that equation equals `correctionCoefficient`.

## Watch for

- δ is defined by choice; the file states only its defining equation, not its uniqueness.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LubinTate/FormalModule/RecursiveCoefficient.lean`: the Lean file is the source byte for byte (SHA-256 `a661c2d1315de6a1293311bb87e7121a076d519358fd9464903dddc690a34419`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.

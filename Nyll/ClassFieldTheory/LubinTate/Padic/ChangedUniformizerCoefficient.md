# Witt-vector coefficients for the p-adic changed-uniformizer intertwiner

Module `Nyll.ClassFieldTheory.LubinTate.Padic.ChangedUniformizerCoefficient`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Comparing the Lubin–Tate series of two uniformizers π and π′ = u·π of ℚ_p (u a unit of ℤ_p) needs a power series with coefficients in the ring of integers of the completed maximal unramified extension, semilinear for Frobenius φ. Here that ring is the Witt ring W(k) with k an algebraic closure of ℤ/p. The file supplies the coefficient-level inputs: a unit ε of W(k) with φ(ε) = ε·u, which serves as the linear coefficient, and unique solvability of the coefficient equations in degrees m ≥ 2, stated only with the Witt-vector prime p, the image of the standard uniformizer of ℚ_p, in the factor p^(m−1); a general π does not occur.

## Main definitions

- `padicCompletedUnramifiedWittRing p`: the Witt ring W(`AlgebraicClosure (ZMod p)`).
- `padicIntToCompletedUnramifiedWittRing p`: ℤ_p → W(k), through Mathlib's isomorphism W(ℤ/p) ≃ ℤ_p and the inclusion ℤ/p → k.
- `padicValuationSubringToCompletedUnramifiedWittRing p` and `padicValuationUnitToCompletedUnramifiedWittUnit p`: the same map from the valuation ring of the library's `padicLocalField p`, and on units.
- `padicChangedUniformizerLinearCoefficient p u`: the unit ε, obtained from Mathlib's `WittVector.frobeniusRotation`.

## Main results

- `padicIntToCompletedUnramifiedWittRing_frobenius`, `padicValuationSubringToCompletedUnramifiedWittRing_frobenius`: Witt Frobenius fixes the image of ℤ_p.
- `padicValuationSubringToCompletedUnramifiedWittRing_uniformizer`: the standard uniformizer goes to p.
- `completedUnramifiedWittUnit_coeff_zero_ne_zero`, `padicChangedUniformizerRotation_coeff_zero_ne_zero`: nonvanishing of zeroth Witt coordinates, used to make ε a unit.
- `padicChangedUniformizerLinearCoefficient_frobenius`: φ(ε) = ε·u.
- `existsUnique_padicChangedUniformizerCoefficient`: for m ≥ 2 and any b in W(k), the equation a = b + u⁻¹·p^(m−1)·φ(a) has exactly one solution a.

## Proofs

Frobenius fixes the image of ℤ_p because on ℤ/p-coordinates it raises to the p-th power. For the coefficient equation, a ↦ u⁻¹·p^(m−1)·φ(a) maps (p)^n into (p)^(n+1), since φ preserves the ideal (p) and m − 1 ≥ 1; a fixed-point lemma for p-adically complete rings from the library then gives existence and uniqueness.

## Watch for

- The file is specific to ℚ_p, not a general local field: the base is the library's `padicLocalField p`.
- The completed unramified extension is represented only through its ring of integers W(k); no field is constructed here.
- The file prepares the coefficients and does not itself build the semilinear intertwiner.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LubinTate/Padic/ChangedUniformizerCoefficient.lean`: the Lean file is the source byte for byte (SHA-256 `fe3bcb76446f8b9fc6eee38cb37f6eb36d2eb4c9cf673630f00b65f0fb174d9d`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.

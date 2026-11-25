# Unique extension of a Henselian valuation to algebraic extensions

Module `Nyll.ValuedFieldTheory.Valuation.Henselian.AlgebraicExtensionUniqueness`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `V` be a valuation subring of a field `K`, Henselian along its maximal ideal, and `L/K` an algebraic extension. The file shows that every valuation of `L` extending the valuation of `V` has the same valuation ring, namely the integral closure of `V` in `L`.

- `valuationSubring_eq_integralClosure_of_henselianRing`: for any valuation `w` on `L` extending that of `V`, the valuation subring of `w` equals, as a subring of `L`, the integral closure of `V` in `L`.
- `valuationSubring_eq_of_henselianRing`: any two such valuations `w₁`, `w₂` have the same valuation subring.

The proof uses a result from an imported file, that the integral closure of `V` in `L` contains `z` or `z⁻¹` for every `z : L`, and a lemma identifying the valuation ring of any extension with an integral closure that has this property.

The conclusion is stated as equality of valuation subrings; equivalence of the valuations is not stated here, though it follows by Mathlib's `Valuation.isEquiv_iff_valuationSubring`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/Henselian/AlgebraicExtensionUniqueness.lean`: the Lean file is the source byte for byte (SHA-256 `46b6498ba1c4048d3c63de1446538deaa3763ffc2789718a215f91446aa15ebb`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.

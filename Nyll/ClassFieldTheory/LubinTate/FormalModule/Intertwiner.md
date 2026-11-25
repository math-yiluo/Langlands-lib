# The intertwining equation for Lubin–Tate series

Module `Nyll.ClassFieldTheory.LubinTate.FormalModule.Intertwiner`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For two Lubin–Tate series e, ē with the same linear coefficient π over the valuation ring of a local field K, the file defines the multivariable equation e(H) = H(ē(X₁), …, ē(Xₙ)) for a power series H, and its additive defect.

## Main definitions

In `LubinTate.SameUniformizer`:

- `inVariable e i`: the series e(Xᵢ).
- `Intertwines e ebar H`: the proposition e(H) = H(ē(Xᵢ)ᵢ), with one-variable substitution on the left and multivariable substitution on the right.
- `defect e ebar H`: the difference e(H) − H(ē(Xᵢ)ᵢ).

## Main results

- `constantCoeff_inVariable`, `inVariable_hasSubst`: e(Xᵢ) has zero constant coefficient, so for finitely many variables the family can be substituted.
- `intertwines_iff_defect_eq_zero`: H intertwines iff its defect is zero.
- `intertwines_X`: for finitely many variables, each variable Xᵢ intertwines e with itself.

## Watch for

- `Intertwines` does not require H to have zero constant coefficient, the condition that guarantees that H can be substituted into e; later files assume it, for instance through a prescribed linear term.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LubinTate/FormalModule/Intertwiner.lean`: the Lean file is the source byte for byte (SHA-256 `826e93f0498a94fdae9486203e4fd75023cc112ebaf6946b19ef63670b27eda1`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.

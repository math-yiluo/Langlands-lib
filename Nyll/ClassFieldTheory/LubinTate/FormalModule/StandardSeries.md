# The standard Lubin–Tate series

Module `Nyll.ClassFieldTheory.LubinTate.FormalModule.StandardSeries`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a local field K with residue field of q elements and a uniformizer π, the polynomial f(X) = π·X + X^q is a Lubin–Tate series. It serves as the canonical input of the formal-group construction, in any characteristic.

## Main definitions

- `standardLubinTatePowerSeries F π`: the power series π·X + X^q over the valuation ring, defined for any element π.
- `standardLubinTateSeries hπ`: the same series as a `LubinTateSeries F π`, given that π is a uniformizer.

## Main results

- `LubinTateSeries.standardLubinTateSeries_toPowerSeries`: the underlying series is π·X + X^q.

## Proofs

The constant coefficient vanishes and the linear coefficient is π because q > 1; the reduction is X^q because π reduces to zero.

## Watch for

- The uniformizer hypothesis is needed only for the reduction condition.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LubinTate/FormalModule/StandardSeries.lean`: the Lean file is the source byte for byte (SHA-256 `a7ca516fae8c24d5115ff1fa27bc1622f6799823716776224c0742795f2ab072`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.

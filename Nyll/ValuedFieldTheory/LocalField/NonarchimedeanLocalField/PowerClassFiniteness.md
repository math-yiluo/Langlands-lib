# Finiteness of Kˣ/(Kˣ)ⁿ for a local field

Module `Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PowerClassFiniteness`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The single theorem `finite_nthPowerQuotient_of_natCast_ne_zero` says: for a nonarchimedean local field `K` and a natural number `n` with `(n : K) ≠ 0`, the quotient of `Kˣ` by the subgroup of `n`-th powers is finite. The module comment names it as the finiteness input for maximal Kummer extensions and the characteristic-zero local existence theorem.

The proof passes to the normalized valuation `localIntegerValuation` and splits by characteristic. In characteristic zero the principal units `U¹` are isomorphic to `ℤ/p^a × ℤ_p^d` with `d = [K : ℚ_p]`; in characteristic `p` the hypothesis means `p ∤ n`, and `U¹` is isomorphic to a countable product of copies of `ℤ_p`. In both cases `U¹/(U¹)ⁿ` is finite, and an imported result passes from principal units to `Kˣ` using a uniformizer.

The hypothesis excludes `n = 0` and, in characteristic `p`, every `n` divisible by `p`. The structure theorems for `U¹` used here are imported from other files of the library.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/PowerClassFiniteness.lean`: the Lean file is the source byte for byte (SHA-256 `1deaa9fd7f40add94f5e9504e3c3d7627eb20041d73c7abb378d40df88b841a2`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.

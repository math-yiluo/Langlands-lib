# Complete splitting of a finite prime

Module `Nyll.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.FinitePrimeSplitsCompletely`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The condition that a finite prime of a number field `K` splits completely in an extension `L` that is itself a number field.

- `FinitePrimeSplitsCompletely K L v`: every finite prime `w` of `𝓞 L` lying over `v` has ramification index `1` and inertia degree `1` over `𝓞 K`.

## Points to watch

The condition is stated prime by prime, through `e = f = 1`, not by counting `[L : K]` primes above `v`, and no Galois hypothesis on `L/K` is made.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/Definitions/FrobeniusAndHilbertClassFields/FinitePrimeSplitsCompletely.lean`: the Lean file is the source byte for byte (SHA-256 `8de6966cbfffc4ba5af899096dd452c2fe4141939cd4e8d7b0cf30a280304b24`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.

# The fractional ideal of a finite prime

Module `Nyll.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.FinitePrimeFractionalIdeal`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

A finite prime of a number field `K` seen as an element of the group of nonzero fractional ideals.

- `finitePrimeFractionalIdeal v`: for `v : HeightOneSpectrum (𝓞 K)`, the prime ideal `v` coerced to a fractional ideal of `K`, as a unit of the fractional ideals (`NumberFieldFractionalIdealGroup K`); it is nonzero because `v` is.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/Definitions/FrobeniusAndHilbertClassFields/FinitePrimeFractionalIdeal.lean`: the Lean file is the source byte for byte (SHA-256 `d1ff4604785e83dd3e0a0f86b717117f397ad91fa0e06713ef468793b9ad582c`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.

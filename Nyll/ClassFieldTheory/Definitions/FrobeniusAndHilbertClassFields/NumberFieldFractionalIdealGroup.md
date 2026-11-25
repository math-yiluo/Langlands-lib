# The group of fractional ideals of a number field

Module `Nyll.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.NumberFieldFractionalIdealGroup`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Names the group of nonzero fractional ideals of a number field `K`.

- `NumberFieldFractionalIdealGroup K`: an abbreviation for the unit group `(FractionalIdeal (𝓞 K)⁰ K)ˣ` of the monoid of fractional ideals of `𝓞 K` in `K`, that is, the invertible fractional ideals.

## Points to watch

The group is defined as the units of the fractional ideals, not as the nonzero ones; the two agree because `𝓞 K` is a Dedekind domain, but the file does not state this.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/Definitions/FrobeniusAndHilbertClassFields/NumberFieldFractionalIdealGroup.lean`: the Lean file is the source byte for byte (SHA-256 `727c57da6b9092d6991d2aae2c8c8d288a8c28b63ce12684148f6547d087d83a`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.

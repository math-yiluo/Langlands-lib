# The universe of groups for integral cohomology

Module `Nyll.GaloisCohomology.Cyclic.IntegralRepUniverse`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file contains a single abbreviation, `IntegralRepGroupType := Type 0`.

Mathlib's group cohomology, group homology and Tate cohomology need the coefficient ring and the acting group in one universe. With coefficients ℤ, which lives in `Type 0`, the acting group must then lie in `Type 0`. The abbreviation names this restriction for the constructions that use Mathlib's integral cohomology objects directly.

The universe-polymorphic alternative is the `IntegralGroupCohomology` construction in the integral coefficient cohomology file. It works over `ULift ℤ` and restricts scalars back to ℤ, and it is shown there to agree with Mathlib's objects in universe 0.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/GaloisCohomology/Cyclic/IntegralRepUniverse.lean`: the Lean file is the source byte for byte (SHA-256 `fd817c6ca3b78c6195bc79e30e3c992b7ce326dec94117c4f2bfb1ccccd503f0`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.

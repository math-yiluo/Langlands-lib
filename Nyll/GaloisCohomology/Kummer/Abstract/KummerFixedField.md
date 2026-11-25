# The abstract field K(S)

Module `Nyll.GaloisCohomology.Kummer.Abstract.KummerFixedField`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

In abstract Kummer theory, closed subgroups of a group `G` equipped with a topology stand for fields. For a set `S` in an integral representation `A` of `G` and a closed subgroup `K` (standing for `G_K`), the field `K(S)` corresponds to the elements of `G_K` that fix every member of `S`.

- `setFixingSubgroup A K S`: the subgroup `{σ ∈ G_K | σ s = s for all s ∈ S}` of `G`.
- `isClosed_setOf_representation_fixed`: for a continuous action on discrete coefficients (`IsContinuousDiscreteRepresentation A`), the stabilizer of one element is closed.
- `setFixingSubgroup_isClosed`: hence `setFixingSubgroup A K S` is closed, as an intersection of `G_K` with such stabilizers.
- `closedSetFixingSubgroup`: the same subgroup bundled as a `ClosedSubgroup G`; `mem_closedSetFixingSubgroup_iff` unfolds membership.

Closedness uses that each orbit map `σ ↦ σ a` is continuous into the discrete module.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/GaloisCohomology/Kummer/Abstract/KummerFixedField.lean`: the Lean file is the source byte for byte (SHA-256 `638affcb1b7401b64b54fcc00da5cd82555e33712fd934c2cbc89a31d5bff199`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.

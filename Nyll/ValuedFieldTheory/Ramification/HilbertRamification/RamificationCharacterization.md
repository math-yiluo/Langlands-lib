# The ramification group inside the decomposition group

Module `Nyll.ValuedFieldTheory.Ramification.HilbertRamification.RamificationCharacterization`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a field extension L/K and a valuation subring A of L, the file places the ramification group, which is defined inside the inertia group, in the decomposition group of A.

- `ramificationCondition_mem_inertiaGroup`: suppose σ in the decomposition group satisfies the principal-unit condition: for every x in Lˣ, the unit `automorphismUnitQuotient K A σ x`, which is σ(x)/x, is a principal unit of A. Then σ lies in the inertia group.
- `ramificationGroupInDecomposition`: the image of the ramification group in the decomposition group.
- `mem_ramificationGroupInDecomposition_iff`: membership in this image is exactly the principal-unit condition.

Proof: for nonzero a in A, σ(a) − a = a · (σ(a)/a − 1) has valuation less than 1. So σ fixes the residue of a, and the inertia group is the kernel of the residue action.

Watch for: A is an arbitrary valuation subring. No discreteness and no finiteness of the extension is assumed.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Ramification/HilbertRamification/RamificationCharacterization.lean`: the Lean file is the source byte for byte (SHA-256 `b5984f9ebb43206850fab2851ce282adb26d628f8564c69d4843b2a0c59d4ea2`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.

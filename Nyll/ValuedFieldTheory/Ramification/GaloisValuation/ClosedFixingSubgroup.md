# The closed subgroup fixing an intermediate field

Module `Nyll.ValuedFieldTheory.Ramification.GaloisValuation.ClosedFixingSubgroup`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a Galois extension `Ω / k`, possibly infinite, the file attaches to each intermediate field `K` its fixing subgroup as a closed subgroup of `Gal(Ω/k)` in the Krull topology.

## Main declaration

- `closedFixingSubgroup k Ω K`: the element of `ClosedSubgroup Gal(Ω/k)` whose underlying subgroup is `K.fixingSubgroup`, the automorphisms fixing `K` pointwise. Closedness is Mathlib's `InfiniteGalois.fixingSubgroup_isClosed`.

The file contains this definition only; it proves no lemmas about it. It lives in the namespace `RamificationTheory` and requires `IsGalois k Ω`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Ramification/GaloisValuation/ClosedFixingSubgroup.lean`: the Lean file is the source byte for byte (SHA-256 `750eb12d0e185ae95be4f13ecd9022937f8ce8cdc45b68a80f8d02520593ea50`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.

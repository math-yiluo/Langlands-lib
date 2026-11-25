# Normality of residue extensions for profinite invariant rings

Module `Nyll.ValuedFieldTheory.Ramification.ProfiniteInvariant`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Mathlib shows that residue field extensions are normal when a finite group acts with invariant ring `A`. This file proves the same for a profinite group acting continuously on a discrete ring.

- `RamificationTheory.Ideal.Quotient.normal_of_profinite`: let `G` be a compact, totally disconnected topological group acting on a discrete commutative ring `B` by ring automorphisms fixing `A`. Assume the action is continuous and `A → B` is `G`-invariant (Mathlib's `Algebra.IsInvariant`). Then for maximal ideals `Q` of `B` and `P` of `A` with `Q` over `P`, `(B ⧸ Q)/(A ⧸ P)` is normal.

Proof: stabilizers are open, so each `x ∈ B` is fixed by an open normal subgroup `N`. The finite group `G ⧸ N` gives a monic orbit polynomial of `x` with coefficients from `A`. Its reduction has the class of `x` as a root and splits over `B ⧸ Q`, so the minimal polynomial splits as well.

The discreteness of `B` is essential: it gives finite orbits.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Ramification/ProfiniteInvariant.lean`: the Lean file is the source byte for byte (SHA-256 `dff36f272eed7bae6bb504b156d22cc1804134eef4346610160b9e2d04798940`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.

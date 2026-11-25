# The decomposition field of an absolute value

Module `Nyll.ValuedFieldTheory.Ramification.HilbertRamification.DecompositionField`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a real absolute value `w` on `L` and a subfield `K`, the decomposition field is the fixed field of the decomposition group of `w`. Being phrased with absolute values, it covers archimedean and non-archimedean places alike.

- `absoluteValueDecompositionField K w`: the fixed field of `absoluteValueDecompositionGroup K w` (the automorphisms `σ` with `w(σx) < 1 ↔ w(x) < 1` for all `x`, defined elsewhere).
- `absoluteValueDecompositionGroup_isClosed` (`L/K` algebraic): the decomposition group is closed in the Krull topology. If `σ` moves the class of `w`, one element `x` witnesses it, and the coset of `σ` by the open subgroup fixing `K(x)` avoids the group.
- `absoluteValueDecompositionField_fixingSubgroup_eq` (`L/K` Galois, possibly infinite): the subgroup fixing the decomposition field is the decomposition group, by Mathlib's infinite Galois correspondence.

The decomposition group stabilizes the class of `w`, not `w` itself, and `w` need not extend a given absolute value of `K`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Ramification/HilbertRamification/DecompositionField.lean`: the Lean file is the source byte for byte (SHA-256 `19171d91286c7731ba02b01ae8836ddd53b6147babc9a40ebbe9a36997d7b492`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.

# Induced modules as groups of equivariant functions

Module `Nyll.ProCGroups.InducedFunctions`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a subgroup `H` of a group `G`, with `H` acting on a commutative group `B` (by a multiplicative distributive action), the file defines the induced `G`-module as the group of functions `f : G → B` with `f(hx) = h · f(x)` for `h ∈ H`, and studies evaluation at the identity.

- `inducedSubgroup H`, `InducedModule H`: the subgroup of `G → B` of such equivariant functions.
- `inducedMulDistribMulAction`: `G` acts by right translation, `(g · f)(x) = f(xg)`.
- `inducedEvaluation H`: the homomorphism `f ↦ f(1)` to `B`.
- `inducedEvaluation_smul`: evaluation is `H`-equivariant, with `H` acting on the induced module through the translation action.
- `inducedEvaluation_surjective`: evaluation is onto: for `b ∈ B`, the function equal to `x · b` on `H` and to `1` off `H` is equivariant and takes the value `b` at `1`.

No finiteness of the index of `H` and no topology are assumed; the module is the full group of equivariant functions, with no continuity condition. `B` is written multiplicatively.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ProCGroups/InducedFunctions.lean`: the Lean file is the source byte for byte (SHA-256 `94610f814c2c9c1e9fd31b869de85da36d7913079c09331fa32cb800804ddd28`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.

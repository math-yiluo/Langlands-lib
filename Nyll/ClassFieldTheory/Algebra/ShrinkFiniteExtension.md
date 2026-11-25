# Moving a field extension to universe 0

Module `Nyll.ClassFieldTheory.Algebra.ShrinkFiniteExtension`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a field extension L/K whose fields are `Small.{0}`, this file builds the extension `Shrink K → Shrink L` between their copies in `Type 0`, using Mathlib's ring isomorphisms `Shrink.ringEquiv`, and transports structure to it. Everything is stated in the namespace `HasseArf`.

- `shrinkAlgebra K L`: the algebra structure on `Shrink L` over `Shrink K`, defined from the algebra map of L/K and the two isomorphisms; it commutes with them (`shrinkAlgebra_commutes`, `shrinkAlgebra_apply`).
- `shrink_finiteDimensional`, `shrink_isAbelianGalois`: finite dimension and the abelian Galois property pass to the copy.
- `shrinkGalEquiv`, `shrinkGalMulEquiv`: Gal(Shrink L / Shrink K) ≅ Gal(L/K) by conjugation with the isomorphism of L, as a bijection and as a group isomorphism; `shrinkGalEquiv_apply` gives its value.
- `shrink_isScalarTower`: for a tower K ⊆ E ⊆ L, the three transported algebra structures form a scalar tower.

`shrinkAlgebra` is a definition, not an instance; each statement installs it locally, so results apply only to this particular algebra structure on the shrunk fields.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/Algebra/ShrinkFiniteExtension.lean`: the Lean file is the source byte for byte (SHA-256 `a649e9f9a1978034937f0558d6757ff03040591e18de3a21aa33ba3c2721c57c`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.

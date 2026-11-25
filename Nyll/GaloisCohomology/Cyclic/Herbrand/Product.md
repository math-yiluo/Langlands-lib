# Herbrand quotient of a finite product

Module `Nyll.GaloisCohomology.Cyclic.Herbrand.Product`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite group G, an element σ and a finite family of commutative groups `A i` with G-actions, the product `∀ i, A i` carries the componentwise action (a local instance, `piMulDistribMulAction`).

`herbrandQuotient_pi`: if every `HerbrandH0 G (A i)` and every `HerbrandHMinusOne G (A i) σ` is finite (the library's groups in degrees 0 and −1, the second depending on σ), then so are those of the product, and its Herbrand quotient is the product of the Herbrand quotients of the factors.

The proof counts elements: the imported isomorphisms `herbrandH0PiEquiv` and `herbrandHMinusOnePiEquiv` split both groups of the product into products, and the quotient of cardinalities distributes over the finite product.

The modules are written multiplicatively, the Herbrand quotient is the library's `herbrandQuotient σ` with values in ℚ, and the index type is finite. The statement itself does not assume that σ generates G.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/GaloisCohomology/Cyclic/Herbrand/Product.lean`: the Lean file is the source byte for byte (SHA-256 `20f1ad97a0c6a114afaf1f6160e97f58052f0fd6e2bacb3e11024df33e8fc4cd`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.

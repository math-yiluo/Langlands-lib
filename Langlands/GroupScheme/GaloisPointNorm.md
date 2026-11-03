# Finite-Galois point norms for commutative affine group schemes

This derived construction takes an arbitrary actual commutative affine group scheme over a field and a finite-dimensional Galois extension in the same arbitrary universe. The commutativity belongs to `CommGroupScheme`, not to an auxiliary point model. No splitting or torus hypothesis is used.

`conjugateProduct` is the multiplicative map taking the product of all coefficient-automorphism translates. The full finite Galois group is the index set. Left multiplication permutes that set, proving the product is fixed. `norm` applies the inverse of the constructed `GaloisPoint.fixedEquiv` to this fixed product. It is a monoid homomorphism into the actual base-field coefficient-point group.

`extend_norm` specifies its value after the injective extension. `norm_extend` gives the degree-power formula using the equality between the automorphism-group order and the field-extension degree. `norm_naturality` proves compatibility with actual morphisms of commutative group schemes, by coefficient naturality and preservation of finite products.

The coordinate descent is the previously constructed effective descent, with no witness assumed by this norm. This module supplies algebraic infrastructure for the later KP torus norm image; it does not assert field-choice independence, tower transitivity, openness, unit-norm surjectivity or an Iwahori subgroup.

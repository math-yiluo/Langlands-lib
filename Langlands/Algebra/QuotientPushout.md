# Quotients of a pushout square

This internal helper supports the polynomial relation descent in Stacks 00QV. It considers a pushout `Q'` of `Q` along `A → B` and any ideal `I` of `Q`. The algebra structure from `Q/I` to `Q'/I Q'` is supplied, with the scalar tower and agreement with the original map explicitly assumed. The conclusion states that these actual quotient maps form a pushout. There is no finiteness, injectivity or flatness hypothesis on the ideal or rings.

The proof composes Mathlib's tensor-quotient equivalence with the quotient of the original pushout equivalence. The ideal equality follows from the original equivalence on pure tensors. The resulting equivalence has precisely the canonical quotient value on `1 ⊗ q`, so it proves the pushout assertion for the supplied maps.

This is derived ring infrastructure; it is not a new assumption on Stacks 00QV. Applied to polynomial rings, it identifies extension of the polynomial relations with base change of the quotient. Its provenance is the elementary universal properties of tensor products and ideal quotients as implemented in pinned Mathlib's `TensorProduct.Quotient` and `IsTensorProduct` modules.

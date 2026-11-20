# Interchanging indexed and binary tensor products

For two families of vector spaces `V i` and `M i` over a field, indexed by the same finite type, `Langlands.FiniteTensor.pairTensorEquiv` takes the tensor of the indexed products to the indexed product of the pairwise tensors. It sends `(⊗ᵢ vᵢ) ⊗ (⊗ᵢ mᵢ)` to `⊗ᵢ (vᵢ ⊗ mᵢ)`. The index type may be empty.

The map uses Mathlib's `PiTensorProduct.map₂` with the binary tensor constructor at each index. To prove bijectivity, the implementation takes bases of the two families. The two tensor bases are indexed by pairs of tuples and tuples of pairs, respectively. The pairing map sends each vector of the first basis to a vector of the second basis by pairing the two indices in each position. The resulting basis equivalence gives bijectivity of the original map.

`pairTensorEquiv_map` proves compatibility with arbitrary componentwise linear maps in both families. It checks the equality on pure tensors and extends across finite linear combinations. For the coefficient space of block induction, this moves operators on the local standard modules to one indexed product, with the identity on the indexed product of their multiplicity spaces.

This is an internal algebraic construction from Mathlib's indexed and binary tensor-product APIs.

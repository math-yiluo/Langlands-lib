# Pure tensors of test functions on a finite product

For a finite family of topological spaces `X i`, `SchwartzBruhat.piTensor f` is
the external product `x ↦ ∏ i, f i (x i)` of Schwartz–Bruhat functions
`f i` on the factors. It is locally constant because the product of finitely many
eventually constant functions is eventually constant. Its closed support lies in
the product of the compact closed supports of the factors, so it has compact
support. `piTensor_apply` gives the pointwise formula, and `support_piTensor`
identifies its support with the product of the factor supports.

`span_piTensor` proves, for Hausdorff factors, that these pure tensors span the
whole Schwartz–Bruhat space of the product over `ℂ`.

## Proof of the spanning theorem

The proof uses induction on finite index types (`Fintype.induction_empty_option`).

- *Reindexing.* A bijection between index types induces a homeomorphism of the
  products. Pulling test functions back along it is a linear map sending pure
  tensors to pure tensors, so the spanning property transfers.
- *Empty index.* The product is a point. Every test function is its value times
  the empty pure tensor, which is the constant function one.
- *Adding an index.* The product over `Option α` is homeomorphic to
  `X none × ∏ i : α, X (some i)`. The Library's finite tensor decomposition
  `SchwartzBruhat.exists_tensor_expansion` writes the transported function as a
  finite sum of products `g₀ j (x) * g₁ j (y)`. By induction, each `g₁ j` lies in
  the span of pure tensors on the smaller product. For fixed `g₀ j`, the map
  `g ↦ g₀ j ⊗ g` pulled back to the original product is linear. It sends a pure
  tensor on the smaller product to the pure tensor with first factor `g₀ j`.
  Hence each summand, and the sum, lies in the span.

The private helpers `testPullback` and `optionProductHomeomorph` only package
the pullback along a homeomorphism and the standard `Option` product
homeomorphism.

This is an internal Library lemma. It is used for the product factorization of
twisted characters on block Levi groups in the proof route of Henniart–Lemaire
II.4.5. It does not concern integrals or representations.

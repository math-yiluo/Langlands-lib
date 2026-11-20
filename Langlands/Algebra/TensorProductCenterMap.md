# The center of a tensor product over a field

`TensorProductCenter.centerEquiv` identifies the tensor product of the associative centers of two algebras over a field with the associative center of their algebra tensor product. On a simple tensor it applies the two center inclusions.

To prove surjectivity, the Lean proof expands a central tensor in a basis of the right factor. Commutation with each tensor `a ⊗ 1` implies that every coefficient in the left factor belongs to its center. The inclusion obtained by tensoring the left center into the left factor is injective by flatness over the field. The lifted tensor therefore commutes with each `1 ⊗ b`. Swapping the factors and applying the coefficient argument again brings the tensor into the tensor product of the centers. Flatness also gives injectivity of the tensor of the two inclusions.

This is a derived algebraic construction used to generate the global enveloping center from the centers of the matrix blocks in the totally complex bridge.

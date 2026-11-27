# Normalized refined Jacquet restriction of external tensors

`Langlands.RefinedJacquetTensor.LocalFieldRefinedJacquetTensorStatement`
works over any nonarchimedean local field with its specified
`LocalFieldData`. The input is an ordered matrix Levi, a standard
refinement inside it, and a family of complex representations of the
outer general linear blocks. The field and representation universes
are independent. The families include the empty family in rank zero.

The proposition asserts an equivariant linear equivalence from the
actual upper normalized refined Jacquet quotient of the external tensor
to the external tensor of the actual upper normalized factor quotients.
The target action is pulled back along the inverse of `refinedLeviEquiv`.
The comparison sends the refined quotient class of each pure tensor to
the tensor of the individual quotient classes.

The statement is the product-subgroup coinvariant comparison
`RefinedOppositeJacquetTensor.coinvariantsEquiv` with the outer Levi
and each parabolic Jacquet carrier expressed in block coordinates.
The refined modulus is the product of the inner moduli, so its inverse
half supplies the same action as the tensor of the factor normalizations.

Bernstein and Zelevinsky define the normalized quotient in §1.8(b),
state tensor compatibility with an external factor in §1.9(g), and
identify Levi-in-Levi maps for ordered block refinements in §§2.2–2.3.
The proposition applies the quotient formula to the product of the
inner radicals and specifies its action on every pure tensor.

- `bernstein-zelevinsky-1977-induced-i`, SHA-256
  `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`,
  §§1.8(b), 1.9(g), and 2.2–2.3, printed pp. 444–446.

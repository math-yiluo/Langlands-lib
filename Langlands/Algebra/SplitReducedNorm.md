# The determinant law of a split algebra

This is an internal helper for the general reduced norm construction. Given a
field `K`, a unital `K`-algebra `A` and a matrix chart
`e : A ≃ₐ[K] Matrix I I K` with finite nonempty `I`, `tensorChart` extends the
chart to every commutative `K`-algebra `R` by the tensor universal property.
Its value on `r ⊗ a` is `r` times the coefficientwise image of `e a`.
`splitNorm` is the determinant of this actual algebra map, packaged as a
multiplicative map with zero. The size is `Fintype.card I`.

The naturality theorem covers every algebra map `R →ₐ[K] S`. Its proof is
induction on tensors followed by the fact that determinant commutes with a
ring homomorphism. No field, reducedness or injectivity assumption is made
on the test algebras or their maps. The scalar formula follows from the
determinant of a scalar matrix.

The chart independence theorem uses the Library's proved
`Langlands.MatrixAlgebra.exists_unit_conj_of_charts`. It maps the conjugating
unit over `K` to a matrix unit over `R` and proves the same conjugacy on every
tensor. Determinants of conjugate matrices agree over an arbitrary commutative
ring, so the law is independent of the original field-linear chart on all test
algebras. The unit map is `Units.map` of the constructed norm. `splitNormOne`
is its actual group-theoretic kernel; its membership theorem is the equation
that the norm of the underlying unit value is one. The unit map is natural.

The source convention is Milne, *Algebraic Groups* (2022 corrected reprint),
Remark 24.25, printed p.523 / PDF p.534, registered as
`milne-2022-algebraic-groups`, SHA256
`f2ddd8fa4d263085f173934664b246007a2c0bd539739b7c82de39bfb5d21f40`.
The author errata snapshot of 2026-11-04 has no correction to this passage.
The extension from field-valued points to all commutative test algebras is
the derived construction proved here. This helper assumes a split chart;
it does not yet construct a splitting field, descend a determinant polynomial,
or supply the unconditional reduced norm of a central simple algebra.

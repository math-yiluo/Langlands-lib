# Dimension comparisons under field extension

The theorem
`Langlands.AlgebraicGeometry.SchemeFiberGeometry.fieldExtensionDimensionComparisons`
proves the published proposition `FieldExtensionDimensionComparisons` in three
independent universes u, v and w. The implementation reuses the proof draft
by Worker 105.

For total dimension, `finiteTypeFieldExtensionRingDimensionInvariance`
implements the Noether-normalization argument of the Stacks Project,
Lemma 10.116.5 (tag 00P3), registered as
`stacks-dimension-field-extension-00p3-2026-11-04`, SHA-256
`a952d5dbca6b120b89152bcdcace6f4ad5557de8266de7882430c1954c4d898c`.
The original source is [Lemma 10.116.5](https://stacks.math.columbia.edu/tag/00P3).
For a field extension K/k and a finite-type commutative k-algebra A,
it proves `ringKrullDim A = ringKrullDim (K ⊗[k] A)`.

The zero-algebra case uses the subsingleton tensor product and its bottom
dimension. In the nonzero case, Mathlib's
`exists_finite_inj_algHom_of_fg` produces a finite injective map
k[Fin n] → A. Tensoring with K gives the actual map
K ⊗[k] k[Fin n] → K ⊗[k] A. The theorem
`RingHom.Finite.tensorProductMap` proves finiteness, and flatness over k
proves injectivity. The Library's
`ringKrullDim_eq_of_ringHom_isIntegral_of_injective` compares the dimensions
on each finite injective map. The actual polynomial scalar-extension
equivalence `MvPolynomial.algebraTensorAlgEquiv` and
`ringKrullDim_mvPolynomial_fin` identify both polynomial dimensions with n.
The extension can be arbitrary; A can be reducible or nonreduced.

For pure dimension, `algebraicFieldExtensionPureRingDimensionInvariance`
is an internal application of the separately proved
`flatIntegralPureRingDimensionInvariance`, imported from
`Langlands.AlgebraicGeometry.FlatIntegralPureDimensionProof`.
For an algebraic field extension K/k, the canonical map
A → A ⊗[k] K is integral because an algebraic field extension is integral
and integrality survives base change. It is flat by Mathlib's tensor-product
base-change instance. Its injectivity is proved by composing
`Module.Flat.tensorProduct_mk_injective` with `TensorProduct.comm`;
this gives the required `FaithfulSMul` instance. The flat-integral theorem
then preserves and reflects the dimension d of every minimal-prime quotient.
This applies to arbitrary commutative k-algebras, including zero algebras,
and to infinite and inseparable algebraic extensions, for every natural d.

The final theorem combines these two comparisons. The arbitrary-field-extension
finite-type pure-dimension comparison and filtered scheme-fibre descent
remain with parent task `886bf565-95e9-4dc6-8a9d-73284a523668` revision 1.

# Independence of the local bounded norm image from its splitting field

Let `F` be a nonarchimedean local field, `K = UnramifiedClosure F` its
inertia fixed field in the chosen separable closure, and `E` and `M` finite
Galois intermediate extensions of `K`. Let `T` be an affine commutative
`K`-group. All fields live at arbitrary universe `u`.

`torusNormIwahori_eq_of_le` proves equality of the actual norm images
computed using `E` and `M` when `E ≤ M` and `T_E` is a split torus. The
valuation on each field is the restriction of the prescribed spectral
valuation on `F`'s separable closure. There is no scalar unit-norm
surjectivity premise in this local result.

The proof equips `M` with the algebra structure from the inclusion `E ≤ M`.
Mathlib's `IntermediateField.extendScalars` views the same subfield as an
intermediate extension of `E`, so the existing local unit-norm and
valuation-invariance theorems apply to precisely these carriers and
valuations. Finite dimensionality and the relative Galois property follow
from the finite Galois extension `M/K`. The general norm-image tower
comparison then gives the equality.

`torusNormIwahori_eq_of_splitting_fields` removes the nesting condition. If
both `T_E` and `T_M` split, compare each field with their finite Galois
compositum `E ⊔ M` and compose the equalities. No ordering between `E` and
`M` and no pre-existing equality of their norm images is assumed.
`localTorusNormEquiv` is the induced multiplicative equivalence of the two
subgroups; `localTorusNormEquiv_coe` says it fixes their ambient torus
points.

This is internal infrastructure implementing the splitting-field
independence step of Kaletha–Prasad, *Bruhat–Tits theory: a new approach*
(2023), Lemma 2.5.12, printed pp.89–90 (PDF pp.120–121). The scalar input is
the independently proved inertia-field unit-norm theorem, used via
`nestedIntermediate_unit_norm_surjective`. The correction to Remark
2.5.11's Serre citation points to Chapter V, section 6. This module proves
independence of the torus norm image from its finite Galois splitting field;
it does not assert the full lemma's openness conclusion or the remaining
torus-choice comparison for `H(K)^0`.

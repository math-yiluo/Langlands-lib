# Affine dual-number base change

This is an internal algebra and affine-scheme construction used in the direct
rigidified Picard deformation route. Let `k` and `R` be arbitrary commutative
rings in the same universe, with a specified `k`-algebra structure on `R`.
No field, finiteness, smoothness, or representability hypothesis is used.
All declarations are in
`Langlands.AlgebraicGeometry.Picard.DualNumberBaseChange`.

## Tensor algebra

`tensorTo` is the `R`-algebra map

\[
 R\otimes_k k[\varepsilon]\longrightarrow R[\varepsilon],
 \qquad a\otimes z\longmapsto a\,\operatorname{coefficientMap}(k\to R)(z).
\]

Here the coefficient map is the existing map on both coordinates of Mathlib's
actual dual-number ring. The factor `a` is included as a constant dual number.
`tensorTo_includeLeft`, `tensorTo_includeRight`, and `tensorTo_tmul` prove these
formulas. `tensorFrom` fixes the constant `R`-coefficients and sends epsilon to
`1 ⊗ epsilon`. Its square is zero because epsilon in the second factor squares
to zero. Commutativity supplies the other hypothesis of `DualNumber.lift`.

`tensorTo_comp_tensorFrom` proves the first inverse law by the universal property
of dual numbers: it suffices to check epsilon. `tensorFrom_comp_tensorTo` uses
the universal property of the tensor product and then the same epsilon check
on the second factor. `tensorEquiv` bundles the resulting `R`-algebra equivalence.

`tensorAugmentation` is evaluation at epsilon zero on the tensor product:
it fixes `R` and applies `k[epsilon] -> k -> R` on the second factor.
`augmentation_comp_tensorTo` identifies it with the first-coordinate map on
`R[epsilon]`. `tensorTo_scale` proves that scaling epsilon in the second tensor
factor by `r : k` corresponds to scaling epsilon in `R[epsilon]` by the image of
`r` in `R`. This applies also to zero and nonunits.

For any `k`-algebra map `f : R -> S`, `tensorTo_natural` proves that changing the
first tensor factor by `f` corresponds to applying the existing dual-number
coefficient map. These statements compare the actual algebra maps, not just
their values on a chosen set of coefficients. The proofs check both tensor
inclusions and use the coordinate formulas for coefficient change and scaling.

## Actual affine schemes

`affineThickening k R` is the categorical scheme pullback

\[
 \operatorname{Spec}R\times_{\operatorname{Spec}k}
 \operatorname{Spec}k[\varepsilon].
\]

`affineIso` constructs an isomorphism from this pullback to
`Spec (DualNumber R)`. It composes Mathlib's `pullbackSpecIso`, which identifies
the fibre product with the spectrum of the tensor product, with the spectrum
of the inverse of `tensorEquiv`. This direction accounts for the
contravariance of the spectrum functor.

`affineIso_inv_fst` identifies the first projection after the inverse isomorphism
with `Spec` of the constant inclusion `R -> R[epsilon]`.
`affineIso_inv_snd` identifies the second projection with `Spec` of the
coefficient map `k[epsilon] -> R[epsilon]`. Both follow from Mathlib's projection
formulas and the two tensor inclusion formulas above.

`affineClosedPoint` is constructed independently by the pullback universal
property from the identity on `Spec R` and the spectrum of
`k[epsilon] -> k -> R`. `affineClosedPoint_eq` and
`affineClosedPoint_comp_affineIso` show that it corresponds to the spectrum
of the first-coordinate augmentation `R[epsilon] -> R`.

`affineScale` is the pullback map induced by the identity on `Spec R` and the
spectrum of epsilon scaling on `k[epsilon]`. `affineIso_inv_scale` proves that
it corresponds to the spectrum of epsilon scaling on `R[epsilon]`, with scalar
the image of `r : k`. `affineMap` is the pullback map from the thickening of
`Spec S` to that of `Spec R` induced by `Spec f`.
`affineIso_inv_natural` proves compatibility with the spectrum of the existing
coefficient map on dual numbers. These scheme equalities are proved by
pullback extensionality, the projection identities, and coordinate calculations.

## Provenance and scope

The construction is derived internally from the tensor-product and dual-number
universal properties and Mathlib's actual scheme pullback comparison.
It reuses the published `coefficientMap`, `coefficientAlgMap`, and `epsilonScale`
in `Langlands.GroupScheme.GeneralLinearDualNumber`. No new literature claim or
unproved mathematical comparison is assumed.

This contribution establishes the affine comparison and its specified
compatibilities. It does not identify the full structure sheaf of an arbitrary
nonaffine thickening with split dual-number section rings, classify line-bundle
deformations, compare Cech and derived cohomology, or prove the host tangent/H1
statement. Those comparisons remain separate obligations.

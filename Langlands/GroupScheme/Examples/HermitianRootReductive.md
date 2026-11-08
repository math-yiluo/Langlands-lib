# Connected reductivity of the actual weighted Hermitian group

This internal derived unit proves connected reductivity of
`HermitianRoot.SchemeModel.groupScheme k L H w hw`, the actual affine
scheme equalizer of inverse adjoint and identity in the Weil restriction of
special linear matrices. The coefficients are a separable quadratic field
extension `L/k`; the finite decidable middle index is in `Type`; the base
fields share an arbitrary universe. The diagonal Hermitian weights have
specified unit witnesses `w` with their actual value equality `hw`.
No anisotropy or characteristic restriction is required.

`HermitianRoot.SchemeModel.splittingIso` identifies its scalar extension to
`L` with the full actual special linear group on `Index Middle`. The
pivot `Sum.inl ()` supplies the nonempty index required by the proved
special-linear geometry. `smooth_groupScheme` transfers smoothness along
this actual group-scheme isomorphism and descends it through the
surjective, flat, quasi-compact scalar map `Spec L → Spec k`.
`isAffineHom_groupScheme` uses the established affineness of the equalizer.

`connectedSpace_groupScheme` transfers scheme connectedness from the
special-linear model across the splitting homeomorphism and then through
the continuous surjective projection from the scalar extension. This is
connectedness of the underlying scheme, rather than a statement about its
rational points.

`geometricSplittingIso` factors `k → k̄` through
an embedding `L → k̄`, which exists because `L/k` is finite. Composition of
actual pullback isomorphisms, the constructed splitting, and the actual
special-linear base-change comparison identifies the geometric extension
with the special-linear model over `k̄`.
`hasTrivialGeometricUnipotentRadical_groupScheme` transfers the previously
proved triviality of that model's unipotent radical along this isomorphism.
`isConnectedReductive` assembles these four properties using the existing
Library definition.

The provenance is internal: the implemented proof adapts the established
`QuasiSplitUnitaryReductiveProof` descent argument to the independently
constructed weighted special-unitary splitting and the special-linear
geometry and radical proofs. It introduces no reductivity assumption on
the Hermitian model. Finite Weil restriction of this model, classification
of general relative-rank-one groups, and the unrestricted local
Kneser–Tits theorem remain separate obligations.

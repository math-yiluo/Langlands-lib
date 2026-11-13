# General Hermitian matrix points on all test schemes

This internal construction extends the published `HermitianRoot` tensor matrix
infrastructure to any finite nonsingular Hermitian Gram matrix. The fields
`k` and `L` share an arbitrary universe and have the existing separable quadratic
extension structure. No characteristic is excluded. The finite matrix index
has its own arbitrary universe.

For every relative test scheme `T` over `Spec k`, `tensorForm` maps the actual
invertible Gram matrix into `SpecialLinear.WeilRoot.tensorAlgebra k L T`.
The involution is exactly `SU3Root.SchemeModel.coefficientInvolution`.
The included scalar coefficients respect conjugation by the published
`HermitianRoot.SchemeModel.tensorInclusion_bar` lemma. In particular no
chosen rational point or replacement coefficient ring enters the construction.

`tensorPoints` is the actual determinant-one isometry subgroup of this form.
`tensorPointsMap` is entrywise application of the existing `tensorMap` for every
test morphism. The mapped Gram identity and involution compatibility prove
both defining equations survive restriction. The matrix formula and the
identity/composition laws are explicit; `pointFunctor` bundles them into a
contravariant group-valued functor on all relative test schemes.

`tensorMatrix` extends an arbitrary actual invertible change of basis.
Its restriction compatibility and the general coefficient-congruence lemma
supply `tensorGramCongruence` and `tensorIsometryEquiv`. Their naturality is
proved in the actual determinant-one subgroups for every test restriction.
This supplies point-functor transport and asserts no classification or
representability of a general Gram matrix group.

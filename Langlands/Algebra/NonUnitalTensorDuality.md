# Compatible-input tensor–dual natural isomorphism

Internal derived infrastructure for Renard (9 July 2026), I.4.2, Theorem,
printed pp.23–24 / PDF pp.29–30, registered source
`renard-2026-representations-groupes-reductifs-padiques`.

The module completes the published compatible-input curry/uncurry maps of
`NonUnitalTensorDualMapsParts` to a natural isomorphism. For an S–R bimodule X
nondegenerate on both sides and satisfying `InputCompatible`, it compares
the S-opposite nondegenerate part of `Hom_(R.op)(X, D_R(M))` with
`D_S(X ⊗_R M)`, for every nondegenerate left R-module M.

The component sends h to the balanced functional taking `x ⊗ m` to `h(x)(m)`;
its inverse sends a functional ell to `x ↦ (m ↦ ell(x ⊗ m))`.
The imported maps already prove coefficient linearity, nondegenerate landing
and equivariance for the original residual S-opposite actions. The two inverse
identities follow by extensionality, using pure-tensor extensionality on the
tensor dual. Naturality follows from evaluation on pure tensors: both composites
take h, x and m to `h(x)(f(m))`.

These constructions require no finite-dimensionality, unit or universe equality.
They implement Renard's direct tensor–Hom proof under the compatible coefficient
hypothesis isolated in the published statement unit.

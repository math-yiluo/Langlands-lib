# Reductivity of supplied affine central quotients

Worker 358.

`AffineCentralQuotientReductivityStatement` is the `Prop`-valued definition
of the assertion below. `affineCentralQuotientReductivity` proves it using
the parameterized helper theorem in this module.

`RelativeRoot.IsFppfQuotient.isReductive_target_of_central` applies over every
scheme `S`. Its source group scheme `G` is reductive, the actual fppf
homomorphism `q : G ⟶ Q` has kernel subgroup functor `N`, and `N` is contained
in the all-test-scheme centre of `G`. Assuming `Q` affine over `S`, it proves
that `Q` is reductive over `S`.

The proof first descends smoothness along the supplied fppf homomorphism using
`smooth_target_of_surjective_flat_hom_overBase`. At each geometric point of
`S`, the published field theorem `centralQuotientReductive` applies: reductivity
of the source, centrality of the kernel, and the actual quotient condition
all survive base change. These connected reductive geometric fibres supply
the remaining field in `IsReductive Q`.

This is an internal derived consequence of the imported Library theorems. It
extends the published full-centre argument in `Adjoint.RelativeReductivity`
to an arbitrary central kernel. It does not construct the quotient or prove
affinity of a supplied target.

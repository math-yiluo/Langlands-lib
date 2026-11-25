# Reductivity from a semisimple representation with finite kernel

This internal derived module proves the converse of the finite-kernel criterion
conditional on `SemisimpleRepresentationUnipotentStatement`. That premise is
explicit; this module does not prove the normal-unipotent action assertion or
the forward implication of the criterion.

All declarations retain an arbitrary universe `u`.

`hom_eq_one_of_finiteKernel_comp_eq_one` works over every field `k`. For group
schemes `C`, `H`, and `G`, assume `C` is smooth, affine, and connected and that
the full scheme-theoretic kernel of `q : H → G` is finite. If a homomorphism
`a : C → H` has trivial composite with `q`, then `a` is trivial. There are no
smoothness or connectedness assumptions on `H`, `G`, or the kernel. The proof
factors the universal point of `a` through the represented kernel using
`kernelPointsEquiv`. This factor preserves the identity, so the published
`finiteTargetOverHom_eq_one` makes it the identity morphism. Composing with
the kernel inclusion proves the result on all test schemes.

`isConnectedReductive_of_semisimple_finiteKernel` assumes the full
`SemisimpleRepresentationUnipotentStatement.{u}`. Over a perfect field, let
`G` be smooth, connected, and affine, and let `ρ : G → GL_n` have finite
scheme-theoretic kernel. Assume the supremum of its nonzero simple stable
subspaces is the full coordinate space, with exactly the stability and
simplicity predicates used by
`ReductiveFiniteKernelRepresentationStatement`. Then `G` is connected reductive.

For each smooth connected normal unipotent closed subgroup `i : H → G`,
the supplied assertion makes `ρ.restrict i` trivial. Closedness gives
affineness of `H`. The preceding finite-kernel lemma makes `i` trivial,
and hence its range subgroup functor equals the identity subgroup on
every test scheme. This is `HasTrivialUnipotentRadical G`; the ambient
hypotheses give `IsPseudoReductive G`. The published
`perfectFieldPseudoReductive` proves connected reductivity.

The provenance is internal: these results compose the Library's represented
kernel, pointed finite-target rigidity, normal-unipotent action statement,
and perfect-field comparison. The second theorem is a conditional reduction
for the existing target, and is not an unconditional proof of that target.

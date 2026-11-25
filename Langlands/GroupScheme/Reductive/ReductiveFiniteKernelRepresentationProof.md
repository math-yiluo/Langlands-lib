# Reductivity and semisimple representations with finite kernel

`Langlands.GroupScheme.reductiveFiniteKernelRepresentation.{u}` proves the
Library proposition
`Langlands.GroupScheme.ReductiveFiniteKernelRepresentationStatement.{u}`.
It applies in every universe to every smooth connected affine group scheme
over a perfect field, without additional assumptions. The representation is
an actual homomorphism to `GL_n`; semisimplicity is exactly the supremum of
nonzero simple all-affine-test stable subspaces in the published proposition,
and finiteness concerns the full scheme-theoretic kernel.

For the forward implication, `IsConnectedReductive.exists_semisimple_finiteKernel`
chooses a closed faithful representation, takes its finite family of actual
simple composition factors, and forms their direct sum with coordinates
reindexed to `Fin n`. The simple block images span, giving semisimplicity.
Its kernel acts unipotently in the original faithful representation on every
scheme test. After extension to an algebraic closure, the trivial geometric
unipotent radical forces that full closed normal kernel to be finite; fpqc
descent reflects finiteness to the original field. This forward argument
works over every field.

For the converse, apply
`isConnectedReductive_of_semisimple_finiteKernel` with the independently
published `semisimpleRepresentationUnipotent` theorem. Each smooth connected
normal unipotent closed subgroup acts trivially on the semisimple
representation and therefore maps through its finite kernel. The pointed
finite-target rigidity lemma makes that subgroup inclusion trivial. Thus the
group is pseudo-reductive. The published `perfectFieldPseudoReductive` theorem
then gives connected reductivity. Perfectness is used in this last comparison.

The final Lean proof introduces the telescope of the proposition,
uses the forward existence theorem, and applies the converse reduction with
the proved normal-unipotent action assertion. Both implications retain the
original representation, stable-subspace and kernel definitions.

Provenance: this is a proof of the published encoding of J. S. Milne,
*Algebraic Groups* (2017), Proposition 21.60 (a) if and only if (d), printed
p. 442. The source is registered as `milne-2017-algebraic-groups`, SHA-256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.
The forward proof uses composition factors instead of the source's
central/derived product route; the converse follows the source's use of
normal-unipotent action and the perfect-field comparison. The retained
official errata has no correction for p. 442.

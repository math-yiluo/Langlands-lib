# Scalar transport of complete pinned isomorphisms

For arbitrary fields `k` and `K` in universe `u`, an algebraic extension
`K/k`, actual affine group schemes `G` and `H` over `k`, supplied complete
split pinnings `p` and `q`, and a supplied `SplitPinning.Iso p q`,
`SplitPinning.Iso.baseChange` constructs a complete pinned isomorphism between
their scalar extensions.

Its torus and group isomorphisms are the images under the actual scheme
pullback functors. Its root-index equivalence is the original equivalence.
It preserves the inclusion square, full integral root and coroot maps,
simple support and the actual scalar-extended simple-root Lie vectors.
The lemmas `baseChange_torusIso`, `baseChange_groupIso` and
`baseChange_indexEquiv` state these component specifications.

This is an internal deduction from the published pinning, scalar-extension
and pinned-rigidity interfaces. The inclusion square and lattice maps follow
by functoriality. The source and target simple supports are canonically
identified with their originals. The Lie-vector proof applies
`targetMapLinear_schemeScalarExtension_one_tmul`: the differential of the
actual pulled-back group morphism carries the scalar extension of a vector
to the scalar extension of its original image. The supplied isomorphism's
root-vector equation then gives the required target vector.

`baseChange_refl` and `baseChange_trans` prove that this construction preserves
complete pinned identities and composition. The torus isomorphisms and
root-index maps agree by functoriality; the published pinned rigidity theorem
then identifies the complete pinned isomorphisms.

Complete pinnings and their isomorphism are supplied inputs. The construction
imposes no perfectness or characteristic premise. It does not construct
semilinear cocycles, effective descent or the unconditional quasi-split
inner-form existence theorem.

# Restricted tensor products of actual local subquotients

`FiniteAdelicGL.TensorSubquotient` records reference families and a
subquotient of actual finite adelic tensor representations. Both families
consist of nonzero integral-fixed vectors outside the same finite set \(E\).

`TensorSubquotient.ofLocalSubquotients` starts with smooth local representations
and a surjection from a local invariant subspace onto each target factor.
Outside \(E\), compact-open fixed-vector exactness lifts a nonzero integral-fixed
target vector to the corresponding invariant subspace. Choose those lifts as
references for the subspaces and take their images as the source and target
references. At places in \(E\), every stage already contains the place, so zero
references are harmless.

The actual adelic tensor map of the inclusions is injective by
`RestrictedTensor.map_injective_of_injective`. The tensor map of the quotients
is surjective by `RestrictedTensor.map_surjective_of_surjective`. Identify the
tensor of the local invariant subspaces with the image of the injection, then
transport the surjection to this image.

This construction is the finite-place subquotient step in R. P. Langlands,
*On the notion of an automorphic representation* (1979), Lemma 1 and its
proof, printed p. 203, PDF p. 198 of the Corvallis Part I volume
(`langlands-1979-notion-automorphic-representation`). The Lean construction
uses compact averaging to choose compatible references for the local
subquotient diagram.

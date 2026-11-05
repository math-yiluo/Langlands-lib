# Nilradical reductions for generic geometric irreducibility

This internal helper by Worker 1606 supplies reductions for the affine core of
Stacks Project Lemma 37.27.5 (0559). Its final theorem reduces the full spreading statement to the
faithful domain-algebra case.

A surjection whose kernel consists of nilpotents identifies the nilradical of
the source with the inverse image of the target nilradical. Mapping and
contracting prime ideals proves equivalence of their primality. Ring
equivalences are a special case.

For a finite type algebra over a domain, generic flatness provides a nonzero
base element such that its localization is flat and hence torsion free. An
element nilpotent in the fraction-field tensor has a power killed by a nonzero
base scalar. Torsion freeness makes that power vanish in the fixed localization.
When a scalar algebra inverts the chosen base element, injectivity of the
tensor of the localization map shows that the power vanishes in its tensor
fibre as well. The element being specialized and the scalar algebra are both
quantified after the one localization element.

The tensor quotient equivalence identifies tensoring a quotient with quotienting
the tensor by the extended ideal. If the generators of that ideal are
nilpotent, the extended ideal lies in the tensor nilradical. The surjection
criterion above then gives equivalent primality of the two fibre nilradicals.

These are derived internal algebraic lemmas using Mathlib's localization and
tensor quotient APIs and the companion GenericDensity module.

Nilpotence descends from the algebraic-closure tensor to the fraction-field
tensor. The cancellation equivalence identifies the former with extension of
scalars of the latter over the fraction field. The inclusion into a field
extension tensor is injective, since vector spaces are flat and the field map is
injective.

For an arbitrary finite type algebra B over a domain R with fraction field F,
contract the nilradical of the algebraic-closure tensor to an ideal I of B.
The generic hypothesis makes I prime. The quotient C = B/I is therefore a domain
of finite type over R. The base map R to C is injective: a nonzero scalar has
unit image in the generic tensor, so it cannot belong to the contracted
nilradical, which is proper. The tensor quotient criterion transfers generic
geometric irreducibility from B to C. The conditional domain-algebra theorem
gives a localization element for C. The uniform nilpotence theorem gives
another element making every element of I nilpotent in every nearby field
tensor of B. Applying the quotient criterion again and multiplying the two
localization elements gives the asserted reduction.

For a base R with prime nilradical p, set S = R/p and D = S tensor_R B.
The ring S is a domain, D is of finite type over S, and the actual residue field
at p is a fraction field of S. Tensor cancellation transports the generic
hypothesis to D. Applying the preceding conditional reduction over S produces
a nonzero element of S; any representative in R is non-nilpotent. Every field
map from R kills p and hence factors through S. Tensor cancellation then
transports the nearby fibre conclusion from D to B. This proves
`spreading_of_domain_bases`, whose conclusion is the full published affine
proposition and whose premise is the faithful finite type
domain-algebra theorem. The tensor algebra D lives in the maximum of the two
ring universes; the test-field universe remains independent.

The source motivating these derived reductions is the registered Stacks
collection `stacks-generic-geometric-irreducibility-2026-11-04`, file 0559.html,
Lemma 37.27.5 and its reductions. The proof here implements the algebraic
nilradical and generic-flatness route rather than claiming these internal
lemmas are separately numbered source statements.

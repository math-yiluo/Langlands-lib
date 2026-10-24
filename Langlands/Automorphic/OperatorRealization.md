# Realizations under the actual automorphic operators

This internal construction defines `OperatorRealization F n` for a number field
`F : Type u` and every natural rank `n`. It is a subrepresentation of the
concrete operator algebra on `StableAutomorphicFunctions F n`. Its vectors
are therefore actual automorphic functions, stable under finite adelic
translation, standard infinite compact translation and the genuine
enveloping differential action.

The whole operator representation is obtained by restriction. The finite
and compact representations are its compositions with the concrete generator
maps. `envelopingAction` restricts the genuine differential action and proves
that it is a complex algebra homomorphism. `inclusion` is an injective
intertwiner for the entire concrete operator algebra; the three inclusion
identities recover the three actual actions. The published commutation of
finite translation with differentiation descends through this injection.

`formInclusion` embeds the vectors into the existing actual automorphic
form space and intertwines finite translations. Finite smoothness follows
from that faithful map. `toFiniteRealization` takes its invariant image in
the existing finite realization space. `finiteEquiv` is an actual
equivariant linear equivalence onto this image, and `finiteEquiv_inclusion`
identifies its composite with the form inclusion.

The function map `toContinuous` is injective. Its evaluation identities
state actual positive right translation by finite adeles and by the
standard infinite compact subgroup, with the multiplication order shown
explicitly in Lean.

`IsIrreducible` concerns the entire operator representation. It does not
assert irreducibility of the finite restriction. `HasCentralCharacter`
and `IsCuspidal` impose the existing character and cusp conditions on the
actual image in forms. Their equivalences express these conditions on
every realized vector; the character evaluation law and vanishing
constant-term equations follow. All cusp declarations retain the
`CompactSpace (AdeleQuotient F)` hypothesis required by the actual normalized
constant terms.

`generatedOperatorRealization` is the span of the full operator orbit of a
given stable form. Identity puts the form in this span, and the published
orbit-span minimality theorem proves its universal property. A nonzero
input gives a nonzero generated realization.

All content is derived from `OperatorCore`, `FiniteRealization` and the
project's generic orbit-span construction; no new original-literature
claim is made. These are realized subspaces, not the complete category of
automorphic subquotients. No nonzero stable form, irreducible constituent,
cuspidal occurrence, tensor factorization or spectral data is asserted to
exist here. Equality of the stable core with all forms retains the exact
analytic obligations recorded in `OperatorCore`. Full-operator
isomorphism classes and attached spectra are subsequent constructions.

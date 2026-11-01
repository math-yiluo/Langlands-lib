# Actual operator realizations in the entire form space

This internal construction applies the proved actual core equality and
`stableAutomorphicEquiv` from `FullOperatorAction` to the existing
`OperatorRealization` framework. The number field has an arbitrary universe,
every natural rank is retained, and coefficients are complex. It introduces
no new preservation, occurrence or nonzero-form premise.

`operatorRealizationFullFormOrderIso` is an order equivalence from the existing
embedded operator realizations to **all** invariant subspaces of
`fullAutomorphicAction` on the original `AutomorphicForms` carrier. Its forward
map takes the submodule image under the actual core/form identity; its inverse
takes the preimage. The previously published generic
`conjugatedSubrepresentationOrderIso` supplies invariance, the inverse laws and
order reflection, here with the identity automorphism of the operator algebra.
The input covariance is the proved whole-algebra compatibility of the actual
continuous identity. Thus this construction compares the existing realization
framework to subspaces of the entire form space without changing its objects
or existing consumers.

For an existing realization `S`, `S.fullFormImage` is that actual subspace.
`mem_fullFormImage_iff` identifies membership with membership of the same
underlying function pulled back through the inverse identity.
`S.fullFormEquiv` restricts the continuous identity to `S` and its image.
Both carry their existing induced subspace topologies; the restriction and its
inverse are continuous by Mathlib's `ContinuousLinearEquiv.ofSubmodules`.
Its underlying form equals the existing `S.formInclusion`, and its inverse
uses the inverse ambient identity. Evaluation is therefore unchanged.
`fullFormEquiv_operatorAction` and `fullFormRepresentationEquiv` retain every
concrete operator, including finite translation, standard infinite compact
translation and genuine enveloping differentials. These assertions do not
state that differential operators are continuous in the compact-open topology.

`S.fullFormFiniteImage` forgets the extra operators while retaining exactly the
same submodule of forms. The finite generator proves its finite invariance.
`fullFormFiniteImage_eq` proves equality with the already existing
`S.toFiniteRealization` as embedded form subspaces, by the actual witnesses
for their linear images. This is stronger than an abstract finite equivalence
and means the existing finite, local and spectral consumers use exactly the
same finite image. The character and cusp equivalences follow from that
equality; cusp claims keep the explicit compactness of the additive adele
quotient required by the normalized constant-term construction.

`S.fullFormSubrepresentationOrderIso` applies the same covariance construction
to the restricted actions and identifies all their invariant subspaces.
Its simple-order equivalence proves `fullFormImage_isIrreducible_iff` for the
whole concrete operator action. It makes no irreducibility assertion about
finite restriction.

`generatedFormOperatorRealization` applies the existing genuine orbit-span
construction to the inverse image of any supplied automorphic form. The
membership theorem shows the actual form belongs to its full-form image.
The minimality theorem characterizes containment in every existing operator
realization by membership of that same form in its image; surjectivity of
the ambient order equivalence covers every invariant subspace of all forms.
A supplied nonzero form produces a nonzero realization, proved by injectivity
of the continuous ambient identity. No nonzero form is asserted to exist.

Provenance is entirely internal: the published actual orbit-span and
realization constructions, the separately submitted full-form action and
core equality, the generic covariant image/preimage construction and
Mathlib's restriction of continuous linear equivalences. No new identification
with original literature is claimed. This constructs embedded invariant
subspaces and compares them with the existing framework; automorphic
subquotients, irreducible constituent existence, spectral existence,
factorization and classification remain separate obligations.

# Finite-cover descent of discreteness at the twisted base

This is a derived internal helper for global comparison on twisted sites.
It combines the published definitions of lifted local actions in `TwistedOver`
with finite descent of discreteness in `LocalActionDiscretePart`.
It does not assert an analytic finite-cover theorem.

Let a group `G` act on an object `X` by `ρ`, and let `P` be a morphism property
containing identities. The twisted base is the identity map of `X`.
An arrow to this base is determined by its group element: its underlying
map is forced to be the structure map followed by that group element's action.
This gives `hom_to_base_ext`.

Suppose `G` is a topological group. If a local action on an object lifts the
action on `X`, every arrow from it to the twisted base is locally equivariant
for the canonical base action (`isLocallyEquivariant_to_base`).
For an arrow with twist `g` and an open subgroup `K` fixing a local section,
the proof uses the inverse image of `K` under the continuous conjugation
`h ↦ g⁻¹ h g`. An element `h` of that inverse image corresponds to
`k = g⁻¹ h g` in `K`. The two equivariance composites have the same twist,
so `hom_to_base_ext` identifies them.

`HasFiniteBaseSubcovers J` means that every covering sieve of the base
contains a finite family of arrows whose generated sieve still covers.
It assumes neither admissible actions nor equivariance on the selected arrows.

For a module-valued sheaf and a system consisting of lifted local actions,
`isDiscreteSection_base_of_discreteSieve_mem` says that a section at the base
is discrete whenever its discrete sieve covers and finite base subcovers exist.
Choose a finite covering family inside that sieve. Each selected arrow factors
through an object with an admissible action and a discrete restriction of the
section. The finite family of these intermediate objects still covers.
Their arrows to the base are locally equivariant by the preceding conjugation
argument. Sheaf separatedness supplies the section separation required by
`IsDiscreteSection.of_finite_family`, which proves the assertion.

`isDiscreteSection_base_of_locallyDiscrete` applies this argument to every
section of a locally discrete module sheaf. Its conclusion concerns degree-zero
sections. The finite-cover hypothesis remains explicit; this module does not
establish it for an analytic site or prove acyclicity or a derived comparison.

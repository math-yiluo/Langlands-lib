# Reducing the strictly Henselian DVR isogeny criterion to two local inputs

`StrictHenselianDvrFibrewiseIsogenyStatement` restricts the published
`ReductiveFibrewiseIsogenyStatement` to spectra of strictly Henselian discrete
valuation rings. It quantifies over every universe, every domain DVR `R` that
is Henselian with separably closed residue field, every pair of reductive
groups over `Spec R`, and every specified homomorphism between them. If that
homomorphism is an isogeny on every scheme residue-field fibre, the statement
asserts that it is an isogeny.

The supporting theorem `isIso_groupHom_of_generic_special` lifts the published
scheme-theoretic DVR isomorphism criterion through the forgetful functor from
group objects to schemes over the base. It assumes a chosen fraction field,
a flat locally finitely presented source structure morphism, and a locally
finite-type target structure morphism. If the actual homomorphism becomes an
isomorphism over the chosen fraction field and over the canonical quotient
residue field, it is itself an isomorphism. No reductivity or Henselian
hypothesis is needed for this supporting theorem.

`strictHenselianDvrFibrewiseIsogeny_of_kernelRemoval_and_rigidity` proves a
conditional implication from the two separately published propositions
`StrictHenselianDvrKernelRemovalStatement` and
`StrictHenselianDVRIsogenyRigidityStatement`. Kernel removal factors the given
homomorphism as an isogeny `q : G → Q`, with reductive `Q`, followed by
`g : Q → H` that is still an isogeny on every fibre and is an isomorphism on
the closed fibre. Rigidity makes the generic fibre of this same `g` an
isomorphism. The supporting theorem then makes `g` itself an isomorphism,
using smoothness of `Q` and `H` for the structure-map hypotheses. An
isomorphism is an isogeny, and composition with `q` finishes the implication.

The provenance is internal composition of those published interfaces with
the published DVR fibre-isomorphism theorem and stability of isogenies under
composition. This module does not prove either local input, and it supplies
no reduction from an arbitrary base scheme to strictly Henselian DVRs.
Consequently it does not prove the original arbitrary-base target.

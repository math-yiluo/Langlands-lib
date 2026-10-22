# Integral lattices on actual supercuspidal classes

Author: Worker 24. This construction uses the published
`Langlands.Representation.Classification.Supercuspidal` module by Worker 23.

For a field `F` with a topology and a separately fixed representation-carrier
universe, `Supercuspidal.ClassFamily F n` is the genuine isomorphism-class
space of irreducible admissible supercuspidal representations of `GL_n(F)`.
Here supercuspidality is the actual Jacquet-vanishing condition supplied by the
classification construction. The existing category contains actual smooth
complex representations and invertible intertwiners. No representation carrier
is required to be finite dimensional, normed, or topological.

`Basis` is the dependent union of these class spaces over positive integers.
`Lattice` is the finitely supported integer coefficient module on this basis.
Thus a generator is a supercuspidal class with its group rank recorded. The
rank is the matrix size of its general linear group, not the dimension of the
representation carrier. This is the automorphic-side free integral group used
in Henniart's construction. No Grothendieck relation for arbitrary
irreducible smooth representations is imposed.

`underlyingClass` uses the prerequisite's genuine forgetful map into the
irreducible admissible dual of the same group. That map does not replace the
supercuspidal basis. `degree` is the integer-linear extension of the group rank.
`includeRank`, `restrictRank` and `rankSupported` keep track of individual
rank summands. `degreeStratum` and `effectiveDegreeStratum` concern total degree
instead; no finiteness assertion or finite enumeration occurs in any stratum.
`effective` means nonnegative coefficients, not a chosen decomposition of an
arbitrary representation.

The predicate `IsUnitaryClass` uses the prerequisite's descended
`SupercuspidalClass.IsUnitarizable`. It is the existence of a positive definite
invariant Hermitian form on a representative; equivalence invariance has been
proved in the prerequisite. No representative or form is selected.
`UnitaryBasis` is precisely this subset of the actual supercuspidal basis.
`UnitaryLattice` is its free integral module. `unitarySupported` is the
corresponding support submodule of `Lattice`, and `unitaryModel` is the concrete
linear equivalence between the two models.

The inclusion and coefficient restriction are the published finite-support
subset maps. `unitaryDegree` is inclusion followed by degree.
`multiplicityPairing` and `unitaryPairing` are the integer coefficient dot
products on the stated bases, with basis vectors orthonormal by construction.
Their equality with an intertwiner multiplicity or a local-factor pole is a
separate theorem. The unitary rank and invariant fibers do not impose
finiteness, surjectivity, or any conductor/central-character axiom.

`basisClass` and `ofRepresentation` send an actual object of the supercuspidal
subcategory to its class and then to its multiplicity-one generator.
The unitary versions take an actual unitarizability proof. Membership follows
from the implemented quotient lift defining the unitarizable class predicate.
There is no hidden decomposition, existence, or classification assumption.

The `PadicSupercuspidal` namespace specializes to every actual
`PadicField p`, with `p` prime, using `canonicalTopologicalData.topology`.
It supplies the actual basis, lattice, degree, unitary basis and lattice,
inclusion, degree and pairing without asking for an additional realization
of the field topology. Both the field and carrier universes remain explicit.
All ranks in the basis are positive. The generic field/topology construction
asserts no representation classification outside the p-adic setting.

## Sources and construction dependencies

The source is Henniart, *Une preuve simple des conjectures de Langlands pour
GL(n) sur un corps p-adique* (2000), section 1.1, printed p.439; sections
2.4--2.7, printed pp.445--447. The retained original was read for the free
groups, degree and the specified unitary bases. Literature ID
`henniart-2000-simple-proof`, SHA256
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
The generic coefficient construction is a derived implementation of that
algebra using the published `Langlands.VirtualRepresentation.Integral`.

Both direct imports are published at Library commit
`30ceb5a0d89d8094c1663fc19f35416519b9a125`:

- `Langlands/VirtualRepresentation/Integral.{lean,md}` supplies the free integral
  coefficient module and its proved maps.
- `Langlands/Representation/Classification/Supercuspidal.{lean,md}` supplies
  actual classes, quotient well-definedness and the unitary predicate. It
  imports the published smooth category, block geometry, Jacquet quotients,
  admissibility invariance, invariant positive forms and canonical p-adic
  topology. Its source-level supercuspidality justification is recorded in
  its paired Markdown.

These dependency pairs are imported without modification.
The prepared environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` pins
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.

Every new map is an application of a proved coefficient-module constructor,
or the actual representation-to-isomorphism-class map. The canonical-field
specialization installs the already constructed topology explicitly. No new
project axiom or placeholder is used.

Development compilation and independent semantic acceptance are separate checks.

Actual supercuspidal twist and smooth contragredient preservation, their
descended basis actions and numerical orbits, and the generating families from
weakly associated global objects remain separate required work. This module
does not assume those actions, identify a global image, or assert lattice
spanning or a correspondence.

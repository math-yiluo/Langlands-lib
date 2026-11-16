# Units from actual affine etale rank-one Weyl data

For supplied `AffineEtaleUnitCellData` over a commutative local ring, with its
retained residue point above the closed point, the coefficient map reflects
units. The composite map to the residue field is local, so a coefficient whose
image is a unit was already a unit. `coefficientUnit` selects this original
unit and its value lemma recovers exactly the original coefficient. The same
point and openness of the etale projection prove that projection surjective,
because every point of the local spectrum specializes to its closed point.

For an affine reductive group over that local ring, a closed split maximal
torus with fibrewise root datum, a cocharacter isolating a root and its negative,
and supplied opposite root parametrizations, consider the actual relative
cocharacter centralizer cell. Given its dual-number factorization and affine
etale unit-cell data realizing the coroot reflection, exact dual coefficient
transport identifies the image of the normalization scalar with the inverse
beta unit of the affine etale Weyl data. If the retained residue point lies over
the closed point, unit reflection shows that this original scalar is a unit.
This includes local rings with nilpotents; no reducedness hypothesis is used.

This is an internal derivation from the actual cell and pointed etale
constructions. The proofs use the Gamma-Spec equivalence, locality of the map
to the closed residue field, openness of an etale morphism, and the exact
coefficient-transport formula. The full isomorphism theorem and normalization
descent are not asserted here.

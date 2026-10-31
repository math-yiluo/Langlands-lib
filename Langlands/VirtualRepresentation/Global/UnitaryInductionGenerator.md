# Relative generators from actual unitary induction factors

Author: Worker 24.

This derived construction assembles the two integral entries of an existing
`RelativeGlobal.WitnessedGenerator` from actual associated objects and actual
unitary supercuspidal induction data. It combines the canonical full Weil
expansion with the published full induction-factor support encoding.

## Inputs

The number fields `F` and `E`, supplied Galois algebra, fundamental-class
family `c`, finite place `v`, and compactness of the additive adele quotient
are those of `RelativeGlobal.WitnessedGenerator`. The caller supplies an
actual irreducible unitary finite-dimensional relative Weil representation
`S`, an actual cuspidal operator realization `T` of rank `r + 1`, a spectral
presentation `P`, and their genuine weak association. A place above `v`, a
reciprocity candidate, and a continuous local map with its
`IsLocalRelativeWeilMap` proof are also supplied. Local irreducibility and
admissibility refer to the actual local component embedded in the form space.

The additional inputs are an ordered positive block shape `B` of total rank
`r + 1`, an actual supercuspidal object `σ i` for every block, an
`IsUnitarizable` proof for each factor, and an actual invertible intertwiner
`e` from the automorphic local component to their full normalized product.
Each unitarizability proof means existence of an invariant positive definite
Hermitian form. All factor topologies and induction normalizations are those
of the existing canonical p-adic topological data.

The field universe is `uF`; the Weil carrier universe `uW` and the spectral
presentation's factor universe `uP` are independent. The induction factors
here have carrier universe `uF`, so that the normalized induced representation
and the actual form-space local component have the same carrier universe.
No resizing, topology, norm, or finite-dimensionality premise is added to
the smooth supercuspidal carriers.

## Construction and laws

`WitnessedGenerator.ofUnitaryInduction` applies the existing
`unitaryInductionSupport` to all supplied factors, with all multiplicities.
The actual equivalence `e` and local irreducibility give its genuine
`IsUnitaryLatticeSupport` witness by
`isUnitaryLatticeSupport_of_normalizedProductEquiv`. The local object used
here is precisely the canonical `padicObject` of the actual automorphic
local component. Its irreducibility reduces to the supplied proof.

The constructor passes this support to `WitnessedGenerator.ofUnitarySupport`,
which automatically constructs the nonnegative unitary coefficients of the
entire local Weil restriction from continuity, global unitarity, and the
supplied continuous local map. The caller supplies no lattice element,
Weil expansion witness, or automorphic lattice-support witness.

The two projection lemmas identify the resulting entries exactly:

- `ofUnitaryInduction_weilElement` is the canonical full local Weil expansion.
- `ofUnitaryInduction_automorphicElement` is the full induction-factor sum.

`ofUnitaryInduction_automorphicElement_apply` identifies every coefficient
with the exact multiplicity of that unitary cuspidal datum among all supplied
factors. `unitaryInduction_pair_mem` applies the existing generator membership
theorem to put this explicit pair in the existing `pairedLattice`.
The existing witnessed-generator laws then give nonnegativity and equality
of the two degrees to `r + 1`. Automorphic degree counts group ranks; Weil
degree counts the original finite-dimensional carrier.

## Provenance and remaining scope

Henniart, *Une preuve simple des conjectures de Langlands pour GL(n) sur un
corps p-adique* (2000), Théorème 2.4 and section 2.5, printed pp.445–446
(PDF pages 7–8), supplies the intended source application. The theorem's
conclusion gives actual unitary supercuspidal factors whose normalized
product is the local component; section 2.5 uses the full sum of their
classes and the full local Weil restriction. Registered source:
`henniart-2000-simple-proof`, SHA256
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
This module is internal derived packaging of those conclusion data at the
existing finite relative level.

The existing `AssociatedSupercuspidalInductionStatement` retains the theorem
obligation to produce these factors for associated global objects. This
constructor consumes the factors and actual equivalence directly; it does
not assume or prove that statement. It asserts neither existence nor
uniqueness of the associated objects, local map, or factors, and proves no
independence between distinct factor presentations. Unitarity of an arbitrary
local component alone does not supply unitary supercuspidal factors.
Arithmetic fundamental-class instantiation, absolute global Weil comparisons,
support uniqueness, lattice isometry, ambient spanning, and correspondence
existence remain separate obligations. This relative construction does not
complete the broad parent task.

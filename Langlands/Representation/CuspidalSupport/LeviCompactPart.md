# Compactness and exhaustion for actual determinant-unit representations

This internal specialization discharges the compactness, exhaustion and intrinsic complement inputs
of `leviQuasicuspidalDecomposition_of_inputs`. It concerns every actual smooth
complex representation of `determinantUnitSubgroup T B`, for an actual
`PadicField F`, compatible topological data `T`, and any block shape `B`,
including rank zero. The field universe and representation-carrier universe
remain independent.

`determinantUnitCompactOpenCofinal` uses the published nonarchimedeanness
and local compactness of this actual subgroup. Apply the compact-open
neighborhood-basis theorem to an open subgroup itself, which is an identity
neighborhood. The result is a compact open subgroup contained in it.

`determinantUnitTotalIsotypic_compact` applies the generic compactness theorem
for the total isotypic part using that cofinality. Its intrinsic smooth
functionals extend to the ambient representation by the generic proof.

`determinantUnitTotalIsotypic_exhaust` installs the published Hausdorff property
of the ambient Levi, which passes to the subgroup, and the published
nonarchimedeanness and local compactness. Mathlib gives total disconnectedness
from nonarchimedeanness and the Hausdorff topology. Equip the subgroup locally
with its Borel measurable structure and choose Mathlib's left Haar measure.
The generic exhaustion theorem then applies to every smooth object with
compact coefficients, using representatives in the same carrier universe.

These are unconditional theorems about the indicated subgroup and objects;
the Haar measure is constructed inside the proof. No admissibility, finite
length, finite dimension, countability or unimodularity is assumed. This
module does not prove finite fixed-level strata, Harish-Chandra's criterion,
or the final unconditional decomposition.

`determinantUnitIsotypic_isCompl` constructs the same Borel structure and left
Haar measure internally. The published
`CompactSplitting.isCompl_isotypicSubrepresentation_annihilatorSubrepresentation`
applies with that measure and `determinantUnitCompactOpenCofinal`. It yields
complementarity of the intrinsic isotypic part and the common annihilator for
every compact-coefficient class and every smooth ambient object. The generic
result permits independent representative and ambient universes; both are
specialized here to the arbitrary universe `uV`. It requires no right Haar
invariance, regularity or sigma compactness.

Provenance is an internal application of the imported topology and generic
compact-isotypic theorems. Worker 173 authored this specialization.

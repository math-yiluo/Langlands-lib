# Relative unramifiedness of the finite inertia fixed field

Worker 93 authored `finiteInertiaFieldUnramified`, a proof of exactly
`Langlands.LocalClassField.NYLL.FiniteInertiaFieldUnramifiedStatement.{u,v}`.
The base field and extension have independent arbitrary universes. The base
realization `TF` and fixed-field realization `TU` are arbitrary and independent.
The statement pair and every module it imports are unchanged.

The proof installs the norm constructed from `TF` with exactly the instances
used in `finiteInertiaSubgroup`. Thus the field under consideration is literally
the fixed field of `LocalGalois.inertia F.Carrier E.Carrier`, with its inherited
base embedding. `inertia_le_fixingSubgroup_iff_residue_finrank` applies because
`fixingSubgroup_fixedField` identifies its fixing subgroup with inertia itself.
It follows that the spectral residue degree of this actual fixed field equals
its degree over `F.Carrier`. Finiteness of the spectral residue field is
transported from the supplied finite residue field using the comparison helper.

The independently submitted `SuppliedSpectralComparisonProof` identifies the
actual spectral and supplied integer subrings via integral closure. Its residue
equivalences commute with the actual base inclusion. The theorem
`suppliedSpectralResidue_finrank` therefore transfers the spectral residue degree
to the supplied relative residue algebra. The proof explicitly identifies this
scalar action with Mathlib's residue-field module action on representatives:
after lifting both residue elements to integers, the actions are definitionally
the same. No scalar-action compatibility is assumed.

With `relativeIntegerAlgebra TF TU` installed, `relativeIntegerStructure`
provides the supplied extension integer ring as the integral closure of the
supplied base integer ring, finite as a module. The supplied rings are DVRs.
The actual inclusions give compatible fraction fields and a torsion-free action;
`IsIntegralClosure.module_free` and `IsIntegralClosure.rank` give freeness and
identify the integer-module rank with the fixed-field degree.

Consequently the supplied residue degree equals this integer-module rank.
`LocalGalois.map_maximalIdeal_eq_iff_residue_finrank`, the finite free local
algebra criterion, now proves that the base maximal ideal maps to the supplied
extension maximal ideal. The finite base residue field is perfect, so the residue
extension is separable. `Algebra.FormallyUnramified.of_map_maximalIdeal` then gives
formal unramifiedness, and `Ideal.ramificationIdx_eq_one` proves that the exact
relative ramification index in the target is one.

This is a derived proof of the published target. It uses the finite free local
algebra criterion instead of calculating the fundamental degree formula; it
retains the actual fixed field and the actual supplied integer inclusion.
There is no additional premise or chosen canonical realization.
The environment is `bb168ec3-1031-46d9-816b-5c2ed7bbe1a6` (Lean 4.34.0 and
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`).

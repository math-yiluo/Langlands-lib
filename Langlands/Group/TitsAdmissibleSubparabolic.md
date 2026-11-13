# Parabolic subgroups below admissible parabolics

This module is an internal deduction from the published Tits-system theory.
It works for groups in independent arbitrary universes and assumes only
`IsTitsSystem B N π S`. It requires neither saturation nor finiteness.

`exists_admissible_standardParabolic_eq_of_le` considers subgroups
`B ≤ P ≤ Q` with `Q` admissible. The existing admissible standard-form
theorem writes `Q = P_Y` for an admissible type `Y`, and the standard
parabolic classification writes `P = P_X`. The standard parabolic
inclusion criterion gives `X ⊆ Y`. The published downward closure
`IsAdmissibleType.mono` makes `X` admissible. The theorem retains both
the admissible type and its equality with the actual subgroup `P`.

`isAdmissibleParabolic_of_le` proves that a parabolic subgroup `P`
contained in an admissible parabolic `Q` is admissible. Choose a
conjugate `g B g⁻¹ ≤ P`, conjugate both groups by `g⁻¹`, apply the
preceding standard-form result, and conjugate back.

The noncomputable construction `admissibleStandardTypeOfLE` chooses
the admissible type for `B ≤ P ≤ Q` and bundles it with the proved
standard-subgroup equality. It introduces no additional existence
assumption.

The provenance is the combination of
`exists_admissible_standardParabolic_eq` in `TitsApartmentFaces`,
`exists_eq_standardParabolic` and `standardParabolicSubgroup_le_iff`
in the Bruhat and exchange theory, `IsAdmissibleType.mono` in
`TitsApartmentPanels`, and conjugation invariance of admissibility.
This unit supplies an abstract subgroup-containment step for the
maximal pro-p argument. It does not identify a compact overgroup
with a building facet or prove any maximal pro-p conclusion.

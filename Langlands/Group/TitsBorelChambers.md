# Minimal admissible parabolics

For a supplied `IsTitsSystem B N π S` on arbitrary groups in independent
universes, this module proves that conjugates of the distinguished subgroup
`B` are admissible parabolics and are minimal among admissible parabolics
under subgroup inclusion. No saturation or finiteness premise is used.

`isAdmissibleType_empty` witnesses admissibility of the empty type by taking
each generator itself in its component. `isAdmissibleParabolic_conjugate_borel`
then uses the existing equality of the standard parabolic of empty type with
`B` to give admissibility of every conjugate of `B`.

`conjugate_borel_le_iff` gives `g B g⁻¹ ≤ P` if and only if `g ∈ P`, assuming
`B ≤ P`. The forward implication applies the existing parabolic transporter
rigidity theorem to `g⁻¹`; the reverse implication uses closure of `P` under
group operations. Conjugating an inclusion of Borel conjugates by the inverse
of its target representative reduces it to containment in `B`. The transporter
equivalence makes the relative representative belong to `B`, hence it fixes
`B` by conjugation. This proves `conjugate_borel_eq_of_le`.

Finally, an admissible `P = k P_X k⁻¹` contains `k B k⁻¹`. If `P` is contained
in `g B g⁻¹`, the two Borel conjugates coincide. The two containments then
give `eq_conjugate_borel_of_isAdmissible_of_le`.

These are internal deductions from `TitsSystemRestricted` admissibility,
the existing standard-parabolic subgroup and empty-type identity, and
`TitsParabolicRigidity.mem_of_conjugate_le`, using the existing subgroup
conjugation operations. They introduce no external assertion and do not
construct a geometric building or the comparison with one.

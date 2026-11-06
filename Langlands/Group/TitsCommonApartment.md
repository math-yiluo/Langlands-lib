# Common restricted apartments

For an existing `IsTitsSystem B N π S` on arbitrary groups `G` and `W`,
`exists_common_restrictedApartment` proves that any two admissible parabolic
subgroups `P` and `Q` belong to one of the existing restricted apartments.
The universes of the two groups are arbitrary and independent. The proof
requires neither saturation nor finiteness of `S`.

The implementation unpacks the two admissible parabolics as `g P_X g⁻¹` and
`k P_Y k⁻¹` for admissible types `X` and `Y`. The existing Bruhat existence
theorem applied to `g⁻¹ k` gives a factorization `g⁻¹ k = b n c` with
`b, c ∈ B` and `n ∈ N`. Both standard parabolic subgroups contain `B`.
Consequently conjugation by `b` fixes `P_X`, and conjugation by `c` fixes
`P_Y`. Thus the two original subgroups have representatives `g b` and
`g b n` in the same restricted apartment, represented by `g b`.

`commonRestrictedApartmentRepresentative` chooses such a group element.
`mem_commonRestrictedApartment_left` and
`mem_commonRestrictedApartment_right` give the membership of each original
parabolic in its restricted apartment.

This is an internal deduction from `TitsSystemBruhat.exists_mem_cell`, the
standard parabolic subgroup construction, the restricted-apartment membership
equivalence in `TitsApartmentComparison`, and subgroup conjugation. No new
external assertion is introduced. In the root-valuation construction, this
supplies the group-theoretic common-apartment step after an actual facet to
admissible-parabolic comparison has been proved. It does not construct that
comparison, valuation data, or a polysimplicial realization, and does not by
itself establish a building axiom on a geometric quotient.

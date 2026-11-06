# Faces and chambers in restricted Tits apartments

For a supplied `IsTitsSystem B N π S` on groups in independent arbitrary
universes, this module proves two incidence properties of the existing
restricted apartments. It requires neither saturation nor finiteness.
All results are internal deductions from `TitsApartmentComparison`,
`TitsParabolicRigidity`, and `TitsBorelChambers`.

Conjugation preserves admissibility by multiplying its representing group
element. If an admissible parabolic `Q = g P_X g⁻¹` contains `B`, the
existing transporter rigidity `mem_of_eq_conjugate` puts `g` in `Q`.
Conjugating the equality back by `g⁻¹` then makes `Q = P_X`. This proves
`exists_admissible_standardParabolic_eq`, retaining the original admissible
type `X`, rather than merely obtaining some standard type.

Suppose `P` lies in the restricted apartment represented by `a` and is
contained in an admissible `Q`. Write `P = (a n) P_X (a n)⁻¹`.
Since `B` lies in `P_X`, conjugating `Q` by `(a n)⁻¹` gives an admissible
overgroup of `B`. The previous result makes it standard of admissible type.
Conjugating back gives a presentation of `Q` in the same apartment.
This is `mem_restrictedApartment_of_le`. In the reverse-inclusion facet
order, it is closure under taking faces.

Finally, replacing `X` in the same presentation of `P` by the empty type
gives `(a n) B (a n)⁻¹` in the same apartment and contained in `P`.
The empty type is admissible even when `S` is empty, so this proves
`exists_conjugate_borel_le_in_restrictedApartment` without an exception.
The noncomputable `restrictedApartmentBorelRepresentative` chooses its
normalizer element; `restrictedApartmentBorelRepresentative_spec` exports
membership and containment for the resulting Borel conjugate.

These results concern actual subgroups and existing restricted-apartment
sets. They do not construct a polysimplicial realization or assert gallery
connectedness, thinness, thickness, or existence of valuation-building data.

# Two Borel conjugates over an admissible cover

For a supplied Tits system `h : IsTitsSystem B N π S`, with independent
group and Weyl-group universes, `apartmentBorelsBelow B N a Q` is the set
of conjugates `(a n) B (a n)⁻¹`, for `n : N`, contained in `Q`. These are
actual subgroups, so representatives giving the same subgroup count once.
`apartmentBorelsBelow_eq_inter` identifies this set with the intersection
of `borelsBelow B Q` and the existing restricted apartment based at `a`.
The forward direction uses the admissibility of the empty type. In the
reverse direction, a contained apartment Borel is equal to the given
Borel by the previously proved minimality of Borel conjugates.

Right multiplication of the apartment representative by an element of
`N` leaves the set unchanged. Conjugating both the apartment and `Q`
conjugates the set. The module also proves that admissibility of types
descends to subsets, by retaining the witnesses outside the larger type.

The cover hypothesis in the main results states that `Q` is an admissible
parabolic properly containing `B`, and every admissible parabolic `P`
with `B < P ≤ Q` is `Q`. Thus it excludes intermediate admissible
parabolics, without imposing a condition on arbitrary subgroups.
`exists_eq_standardParabolic_singleton_of_cover` proves that such `Q`
is a standard parabolic of singleton type. First the existing
classification makes `Q` standard of an admissible type `X`. Strictness
makes `X` nonempty. Choosing `s ∈ X` gives an admissible singleton
parabolic between `B` and `Q`; its simple representative lies outside
`B`, so the cover hypothesis identifies it with `Q`.

A simple reflection is an involution distinct from the identity.
`mem_closure_singleton_iff` proves by subgroup-closure induction that
the subgroup it generates consists exactly of `1` and `s`. For a lift
`n : N` of `s`, `apartmentBorelsBelow_standardParabolic_singleton`
therefore identifies the apartment Borels below this standard
parabolic with exactly `B` and `n B n⁻¹`. Indeed, the existing Borel
transporter criterion turns containment into membership of a normalizer
representative in the parabolic; Bruhat-cell disjointness forces its
image into the singleton-generated subgroup. The existing equality
criterion for Borel conjugates gives the two alternatives and separates
them.

`encard_apartmentBorelsBelow_eq_two_of_cover` gives the resulting
extended cardinality of two. The final
`encard_apartmentBorelsBelow_eq_two_of_conjugate_cover` applies to an
admissible parabolic covering `a B a⁻¹`. It conjugates the cover back
to one of `B`, applies the standard count, and transports the set and
its cardinality by the injective subgroup conjugation map.

All results are internal deductions from `TitsApartmentFaces`,
`TitsBorelThickness`, and their existing Tits-system and Bruhat APIs.
No external assertion is introduced. Neither finiteness nor saturation
is required. These subgroup counts do not supply a geometric
realization, gallery connectivity, or an unconditional thin apartment
or building construction; transfer to geometric panel facets remains
a separate step.

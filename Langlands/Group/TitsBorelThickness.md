# Three Borel conjugates below a strict overgroup

This internal unit fixes an arbitrary Tits system `(B,N,π,S)` in a group
`G`, with independent universes for `G` and its Weyl group. It uses the
existing `IsTitsSystem` axioms and proved Bruhat and parabolic results.
No finiteness, saturation, root system, or building realization is assumed.

`borelsBelow B Q` is the set of conjugates of `B` contained in the
subgroup `Q`. The two Borel equality lemmas identify equality with
membership of the relative conjugating element in `B`, using the
existing Borel transporter theorem.

`exists_simple_rep_mem_of_lt` proves that every strict overgroup `Q`
of `B` contains a representative `n` of some `s ∈ S`.
The existing classification writes `Q = B⟨X⟩B` for `X ⊆ S`.
The type `X` is nonempty because the empty type gives `B`.
Choose `s ∈ X` and lift it through `π`; the representative belongs
to `Q` by the standard-parabolic membership formula.

`exists_three_borelsBelow_of_lt` constructs three distinct members
of `borelsBelow B Q`: `B`, `nBn⁻¹`, and `bnB(bn)⁻¹`.
Since `s ≠ 1`, the representative `n` does not belong to `B`,
and neither does `bn`. Apply the noncontainment axiom `conj_not_le`
to the representative `n⁻¹` of the involution `s` to find
`b ∈ B` with `n⁻¹bn ∉ B`. The relative-conjugator equality
criterion proves that the second and third Borel conjugates differ.
All three lie in `Q` because their conjugating elements lie in `Q`
and `B ≤ Q`.

`exists_three_borelsBelow_of_conjugate_lt` conjugates this construction
to any strict inclusion `gBg⁻¹ < Q`. Conjugation and its inverse preserve
the subgroup inclusions and distinctness.
`three_le_encard_borelsBelow_of_conjugate_lt` deduces that at least
three conjugates of `B` lie below `Q`, by including the three-element
set of constructed subgroups.

These are internal deductions from the imported Tits-system and
subgroup interfaces, with no new external assertion. They supply the
algebraic chamber count needed for a thickness argument after an actual
facet–stabilizer comparison is supplied. They do not construct a
polysimplicial complex, prove gallery connectivity, or establish the
unconditional root-valuation building construction.

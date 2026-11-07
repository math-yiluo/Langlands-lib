# Algebraic galleries in restricted Tits apartments

This module is an internal deduction from the existing Tits-system axioms,
restricted-apartment definitions, Bruhat decomposition and singleton-panel
results. The ambient and Weyl groups have independent universes.

`IsAdmissibleParabolicCover` records strict containment with no intermediate
admissible parabolic. `IsApartmentBorelStep` records a subgroup in the specified
restricted apartment which covers both endpoints and is their least common
admissible overgroup. Under the reversed stabilizer order, this is precisely the
panel and meet incidence needed for a later geometric gallery step.

For an admissible singleton type `{s}`, the existing subgroup with underlying
set `B⟨s⟩B` covers `B`. To check this, write any intermediate overgroup of `B` as
`B⟨X⟩B`. Strict containment forces `X` to be nonempty. A representative of an
element of `X` lies in the singleton parabolic, so Bruhat-cell uniqueness and
the involution law force that element to be `s`. The resulting inclusion of
generated subgroups proves equality with the singleton parabolic.

If `n` represents `s`, a subgroup containing both `B` and `nBn⁻¹` contains `n`
by the proved Borel-transporter theorem. It consequently contains every cell of
`B⟨s⟩B`, because `⟨s⟩` consists of `1` and `s`. Thus the singleton parabolic
is the least common overgroup of the two Borels. Conjugating the cover by `n`
gives the cover above `nBn⁻¹`; conjugating all this by `a*m`, for `m ∈ N`,
puts the panel and the two Borels in the apartment based at `a`.

Finally, assume explicitly that all singleton simple types are admissible.
Write the image of `m⁻¹*n` as a word in simple involutions, using the proved
generation theorem. Induction on this word supplies gallery steps between the
successive actual normalizer Borel conjugates. In the empty word case, the
remaining normalizer lift is in the kernel and hence in `B`, so its conjugate
Borel is unchanged. This proves reflexive transitive connectivity between any
two normalizer Borel conjugates in that apartment.

The singleton-admissibility premise is essential for this generic statement.
Its proof for actual affine chamber-simple reflections is in
`AffineSimpleAdmissibility`; identification with a particular Tits simple set
remains an explicit comparison obligation. This module constructs no valuation
data or realization and proves no full building axiom.

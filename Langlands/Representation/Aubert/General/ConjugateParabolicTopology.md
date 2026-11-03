# Topology of actual conjugate parabolic data

This derived adapter transports continuity of the Levi projection and compactness
of the actual left coset space under conjugation in an arbitrary topological
group. All subgroups use their inherited topology; all coset spaces are the
existing `Induction.LeftQuotient`, with their quotient topology. The ambient group
has arbitrary universe `uG`. No closedness, separation, local compactness,
nonarchimedean, or representation hypothesis is required.

For a semidirect decomposition `h : IsSemidirectDecomposition P M U`, the
projection is the published actual homomorphism `h.projection : P →* M`.
`continuous_projection_conj` considers any second decomposition `h'` whose
parabolic, Levi, and radical have the literal membership conditions
`x ∈ H' ↔ g⁻¹ * x * g ∈ H`. It proves continuity of `h'.projection` from
continuity of `h.projection`.

The proof uses the published equality `projection_conj`: the original projection
composed with the continuous inverse-conjugation equivalence on the parabolic
equals inverse conjugation of the second projection. Composing with the inverse
Levi homeomorphism expresses the second projection as a composition of continuous
maps. `IsSemidirectDecomposition.continuous_conjugateWithLevi_projection`
specializes this argument to the existing `h.conjugateWithLevi g hMN`, retaining
the specified actual Levi subgroup and its literal inverse-conjugation witness.
It adds no continuity assumption on that transported projection.

`conjugationLeftQuotientHomeomorph g hPQ` sends the actual class of `x` in
`Q \ G` to the class of `g⁻¹ * x * g` in `P \ G`, where
`hPQ : ∀ x, x ∈ Q ↔ g⁻¹ * x * g ∈ P`. It specializes Mathlib's
`Homeomorph.Quotient.congr` to the ambient inverse-conjugation homeomorphism.
The relation defining the left cosets is `y * x⁻¹ ∈ H`; the membership witness
and the group identities verify preservation of precisely this relation.
The inverse sends the class of `x` to that of `g * x * g⁻¹`.
The `_mk` and `_symm_mk` lemmas give these formulas on the existing
`Induction.quotientMap`.

`conjugateLeftQuotientHomeomorph g P` specializes the same construction to
`conjugateSubgroup g P`, whose membership is already defined by inverse
conjugation. Its representative formulas retain the same orientation.
`compactSpace_leftQuotient_conjugateSubgroup` transports the supplied
`CompactSpace (Induction.LeftQuotient P)` through the inverse homeomorphism.
The compactness assertion is a theorem that consumers may install locally;
this file adds no global compactness instance.

The construction is internal and derived. Its declaration dependencies are
`projection_conj` and `conjugationEquiv` in
`Langlands.Representation.Aubert.General.Conjugation` and `Parabolic`,
`IsSemidirectDecomposition.conjugateWithLevi`, `conjugateSubgroup`, and
`mem_conjugateSubgroup` in `ConjugateParabolic`,
`Induction.LeftQuotient` and `Induction.quotientMap` in
`Langlands.Group.LeftQuotient`, and Mathlib's `Homeomorph.Quotient.congr` and
`Homeomorph.compactSpace`. The existing
`QuotientIntegration.leftQuotientHomeomorph` in `CorrectedOrbitCutIntegrals`
is a related more general group-equivalence construction. The present quotient
adapter directly specializes the Mathlib quotient interface already imported by
the generic parabolic files, without importing the GL orbit-integral
constructions from that file. No original-literature assertion is translated.

This supporting unit supplies topology for comparing an actual conjugated
parabolic with another parabolic sharing its actual Levi. It proves neither
same-Levi independence of normalized induction nor the whole
`RationalInducedK0WeylConjugacyStatement`. All representation, genericity,
admissibility, finite-length, and actual-group realization obligations in those
comparisons remain separate.

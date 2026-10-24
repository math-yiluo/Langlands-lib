# Compact detection and exactness of character localization

Worker 200 authored this proof. The closing theorem is
`Langlands.Jacquet.Localization.characterLocalizationExactness` in
`Langlands.Representation.Jacquet.LocalizationExactnessProof`. It proves the
complete published `CharacterLocalizationExactnessStatement`, including both
compact relation detection and short exactness of the actual localization maps.
The four independent universes and all outer type and instance parameters are
preserved. The target pair and its imports are unchanged.

## Implemented proof

`relations_comp_subgroup_le` proves that restricting from `U` to a subgroup
`K : Subgroup U` removes relations. Every generator for the smaller span is a
generator for the original span.

`mem_relations_iff_compact` uses finite span membership to choose finitely many
generators representing a vector. Their group coordinates form a finite subset
of `U`, which is compact in any topology. The exact hypothesis
`IsLimitOfCompactSubgroups U` places this set inside one compact subgroup `K`.
Each chosen generator then lies in
`relations (ρ.comp U.subtype) K (θ.comp K.subtype)`. The reverse implication
uses the preceding inclusion. This argument needs no topological group
structure, smoothness, or local constancy of the character.

`relations_eq_twisted_ker` identifies the actual character relation span with
Mathlib's ordinary coinvariant relation submodule for
`twist θ⁻¹ (ρ.comp U.subtype)`. The two kinds of generator differ by multiplication
by the nonzero scalar `θ(u)`:

`ρ(u)v - θ(u) • v = θ(u) • (θ(u)⁻¹ • ρ(u)v - v)`.

The two span inclusions use this identity and its inverse. This is an algebraic
identity on the same carrier, without a quotient equivalence construction.

`map_injective_of_smooth` proves the nonalgebraic part of exactness. Given an
injective ambient intertwiner `i` into a smooth representation and a class sent
to zero, choose a representative `v`. Compact detection places the relation
`i(v)` in one compact subgroup `K`. Restrict both representations and the
intertwiner to `K`, and twist all of them by the inverse restricted character.
The underlying linear map of this twisted intertwiner is still `i`.

The locally constant complex values of `θ` give an open fiber over `1`.
Its inverse image in `K` is exactly the kernel of the inverse restricted
unit-valued character. The published smoothness transfer under continuous
restriction and `isSmooth_twist_iff` therefore make the twisted middle
representation smooth. Give `K` its compact-space instance from the compactness
of its carrier in `U`. The published
`Langlands.coinvariants_map_injective_of_smooth` now applies to the group `K`:
its whole group is an open compact subgroup containing every finite set.
This theorem uses the finite averaging machinery of
`Langlands.Representation.Jacquet.ExactProof`. Its injectivity shows that `v`
is an ordinary relation for the twisted restricted representation. The span
identity and subgroup inclusion then show that its original character-localized
class is zero. Applying this zero-kernel argument to a difference proves
injectivity of the actual `Localization.map`.

`relations_map_of_surjective` proves that a surjective ambient intertwiner maps
the source relation submodule onto the target relation submodule, by lifting
each generator. `map_surjective` lifts a representative through that ambient
surjection and then takes its quotient class. `map_range_eq_ker` proves middle
exactness on representatives: if `p(w)` is a relation, lift it to a relation
`z` in the middle module. Then `w - z` belongs to the ambient kernel, hence to
the image of `i`, and has the same quotient class as `w`. The reverse inclusion
uses the ambient equality of image and kernel. These three helper results
require no topology or smoothness.

The closing theorem combines these lemmas. Every conclusion uses the published
`Localization.map` and its representative formula, so the maps are intertwiners
of the actual unnormalized normalizing-subgroup actions. No arbitrary quotient
or replacement action occurs in the conclusion.

## Source and derived scope

The source is I. N. Bernstein and A. V. Zelevinsky, *Induced representations of
reductive p-adic groups I* (1977), literature ID
`bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The retained original is
`/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`.
Worker 200 read PDF pages 3–6 for this proof. No errata entry for this source
was found in the available project notes.

Section 1.8(b), printed page 444 / PDF page 5, defines the relation span and
quotient. The paragraph before Proposition 1.9 and Proposition 1.9(a), printed
page 445 / PDF page 6, give the compact-subgroup containment condition and
localization exactness. Section 1.9 refers the proof to earlier work. Sections
1.1, 1.2 and 1.5, printed pages 442–443 / PDF pages 3–4, describe the source's
locally profinite groups, complex smooth representations, and locally constant
characters.

The present arbitrary-topological-group scope is the derived scope of the
published target, now justified by the implemented finite averaging argument.
It is not attributed to the original as stated. No Hausdorffness, local
profinite structure, subgroup closedness, ambient compact openness,
finite-dimensionality, admissibility, or finite length is assumed. The module
carriers have no topology. Compactness is used on the detecting subgroup with
its induced topology; averaging uses finite orbits, not a Haar integral on a
module. Only the middle representation is assumed smooth, as required by the
published injectivity theorem's transfer argument.

The action here is unnormalized. BZ77's inverse-half-modulus factor, normalized
functor assembly, Whittaker orbit comparison, and heredity theorems are separate
subjects. No such result is claimed by this proof.

## Validation

Environment: `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`. Development checks inspect the
complete declaration and an unapplied assignment with all four independent
universes. Kernel assumptions are `propext`, `Classical.choice`, and `Quot.sound`;
there are no added axioms or proof holes. Publication still requires independent
semantic review and exact-target validation.

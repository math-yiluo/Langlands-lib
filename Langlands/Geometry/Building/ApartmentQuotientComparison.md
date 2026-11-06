# Equivariant comparison from an apartment quotient

This module extends `Langlands.Geometry.Building.ApartmentQuotient` with the
equivariant universal property and the common-apartment injectivity argument
used in Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
Proposition 4.4.4 and Corollary 4.4.5 (printed pp. 183–184, PDF pp. 214–215).
The correction to Corollary 4.4.5 in the authors' 2024 corrections, p. 29,
requires the subgroup comparison at every corresponding apartment point.
The declarations here retain that universal quantifier.

The source files are the registered book
`kaletha-prasad-2023-bruhat-tits-new-approach` and corrections
`kaletha-prasad-2024-corrections`. The book's comparison in §9.6.6
(printed p. 367, PDF p. 398) explains the intended eventual application:
compare root filtrations at corresponding apartment points, identify the
point subgroups, and apply Corollary 4.4.5. This module implements only the
abstract group-action step. It does not construct any of those building,
valuation, root-filtration or facet data.

## Data and the equivariant lift

Let `H` be a group, `N` a subgroup, `A` an `N`-set, and
`P : CovariantSubgroupFamily N A`. Write `Q = ApartmentQuotient P`,
with canonical map `apartment P : A → Q`. For an `H`-set `B`, the
subgroup `N` acts on `B` by restriction.

Given an `N`-equivariant map `f : A → B` and
`∀ x, P x ≤ MulAction.stabilizer H (f x)`, `lift` constructs the
`H`-equivariant map `Q → B` sending `[(g,x)]` to `g • f x`.
Representative independence uses both parts of the existing quotient
relation: `n • x = y` and `g⁻¹ * h * n ∈ P x`. The latter element fixes
`f x`; multiplying its action by `g` gives the required equality of images.
`lift_mk` and `lift_apartment` record the values of this construction.

`hom_ext`, `lift_unique` and `existsUnique_lift` prove uniqueness among
equivariant maps with the prescribed apartment values. Their proofs use
that every quotient class is a translate of a canonical apartment point.
`lift_surjective_iff` identifies surjectivity with the explicit orbit-coverage
condition `∀ b, ∃ g x, g • f x = b`.

## Global injectivity

`HasCommonTranslatedApartment P` is a proposition saying that any two
points of `Q` can be written `g • apartment P x` and
`g • apartment P y` with the same `g`. It is a hypothesis, not a
consequence asserted for an arbitrary covariant subgroup family.

`injective_of_common_translated_apartment` proves that an equivariant
map out of `Q` is injective if its restriction to the canonical apartment
is injective and this common-apartment condition holds. The proof puts the
two points in that apartment translate, cancels the action of `g` on their
images, and applies apartment injectivity. This is the injectivity argument
in the proof of KP Corollary 4.4.5.

`lift_injective` applies this argument to `lift`. `liftEquiv` packages the
resulting bijection as a Lean `Equiv`, assuming common source apartments,
injectivity of `f`, and orbit coverage of `B`. `liftEquiv_smul` and
`liftEquiv_symm_smul` prove equivariance of its two directions.

For the previously defined comparison map between two apartment quotients,
`map_injective_of_common_translated_apartment` assumes common source
apartments, an injective apartment map, and
`IsStabilizerCompatible N P'` for the target subgroup family. The latter
ensures that the target apartment map embeds. The theorem applies the same
global argument. `map_bijective_of_common_translated_apartment` adds
surjectivity of the apartment map and uses the existing `map_surjective`.

## Scope and provenance

The universal property and the named common-apartment predicate are internal
group-action formulations derived from the cited quotient presentation and
comparison proof. The construction works with independent universes for the
group, apartment and target. It uses no reductive-group or field hypotheses.

In an actual building application, the common-apartment condition, the
target action and apartment map, every-point fixer inclusion, apartment
injectivity and orbit coverage must still be proved for the supplied data.
Facet preservation, affine charts, actual roots and the five requested KP
axioms are not conclusions of this module. No metric is constructed here.

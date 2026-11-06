# Actual quotient geometry without relative roots

This is an internal derivation from the published actual apartment and quotient
definitions, the root-free sharp-fixer theorem, and the published triviality of
split subtori in an anisotropic group. It takes supplied apartment or local
valuation-building data. It constructs no centralizer or derived cover and
does not establish the unrestricted building-construction statement.

For arbitrary fields and arbitrary universe `u`, an empty actual relative-root
set makes `D.Apartment` a subsingleton: off-root normalization forces every
value of every valuation to be infinity. The published sharp-fixer result then
reduces the canonical point's full fixer to the image of the normalizer
stabilizer. Every normalizer element fixes the singleton apartment, so that
full fixer is exactly `normalizerPoints i`.

The entry `quotientNormalizerEquivOfRelativeRootsEqEmpty` constructs an
equivalence from the actual coset space
`rationalPoints G ⧸ normalizerPoints i` to `D.ReducedBuilding`. It transports
the subgroup by the proved fixer equality and uses Mathlib's injective
orbit-stabilizer map. Surjectivity follows from the original quotient's
representative theorem and equality of all apartment points. The representative
formula sends the class of `g` to `g • D.apartmentMap x`, and the action lemma
proves equivariance for the original rational-point actions.

Each apartment facet is a singleton. For supplied local valuation-building
data with empty actual roots, the building facets are precisely the singleton
subsets of the actual quotient, using the existing translated-facet definition.
Thus the apartment map is injective and every building facet meeting its image
is the image of its unique apartment facet. This proves the existing
`HasCompatibleApartmentFacets` predicate (AS 6). The apartment image is a
singleton with stabilizer equal to its point fixer, which also proves the
existing `HasNormalizerApartmentStabilizer` predicate.

The quotient is not asserted to be a singleton merely from root emptiness.
For an anisotropic group with a supplied split subtorus, the imported
`IsAnisotropic.centralizerPoints_eq_top` from
[`AnisotropicRootSystem`](../../GroupScheme/Rational/AnisotropicRootSystem.md)
states that every rational point centralizes the inclusion. This follows from
equality of all homomorphisms out of that subtorus and implies that every
rational point normalizes the inclusion. Consequently the full
canonical point fixer is the whole rational-point group, and every original
quotient representative equals that point. This supplies
`subsingleton_reducedBuilding_of_isAnisotropic` without a replacement quotient.

These constructions retain all original filtrations, sharp fixers, quotient
relations and actions. They do not assert existence of apartment data, a
polysimplicial realization, an apartment splitting, bounded open stabilizers,
root-reflection witnesses or a Tits system. The general-root construction and
the parent's full conjunction remain separate obligations.

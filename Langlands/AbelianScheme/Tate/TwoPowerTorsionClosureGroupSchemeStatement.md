# A closed group scheme realizing the actual two-power torsion closure

`Langlands.AbelianScheme.Tate.TwoPowerTorsionClosureGroupSchemeStatement.{u}`
asserts the following for every algebraically closed field `K : Type u` and
every actual bundled abelian scheme `A` over `Spec K`. There is a commutative
group scheme `G` over the same base and an actual group-scheme homomorphism
`f : G ⟶ A.toCommGroupScheme` whose underlying scheme morphism is a closed
immersion, whose range is exactly `closure (twoPowerTorsionLocus A)`, and whose
source structure morphism `G.X.hom` is smooth and proper.

The locus is the existing actual two-power torsion locus: images of rational
sections killed by some power of two, using the given section group operations.
The topology and closure are the Zariski topology on the underlying scheme of
`A`. The conclusion supplies actual multiplication, unit and inversion on `G`,
their group laws and commutativity through the `CommGroupScheme` bundle. The
typed morphism `f` preserves the group operations. Smoothness and properness
refer to the map to `Spec K`, while the closed immersion is the map into `A`.

There is no characteristic assumption. The statement does not assert geometric
connectedness or bundle `G` as an abelian scheme. It does not give a dimension
comparison, a torsion cardinality formula or density, and this file defines the
proposition without proving it.

The provenance is an internal geometric prerequisite for the density task.
The motivating original is Edixhoven, van der Geer and Moonen, *Abelian
Varieties*, preliminary version, Chapter V, section 3, Theorem (5.30), printed
page 84 / PDF page 88, registered as
`edixhoven-vandergeer-moonen-abelian-varieties-draft`. The prime-to-characteristic
part of its density argument first makes the reduced torsion closure into a
closed subgroup. The present statement isolates a group-scheme realization;
it does not import that theorem's density conclusion.

The intended independent derivation starts with the actual reduced closed
scheme and its unit, inversion and rational translation restrictions. Closed
points are rational over an algebraically closed field, so restricted
translations act transitively on them. The smooth-locus argument gives
smoothness of the reduced closure. Its product over the field is then smooth
and reduced. Products of rational sections lie in the closure by the existing
section-subgroup theorem. Closed points are dense in this product, so ambient
multiplication has its entire image in the closure. Reducedness allows
factorization through the closed immersion. Unit, associativity, inverse and
commutativity identities follow by cancellation of that immersion from the
ambient identities. Properness follows from its closed immersion into the
proper abelian scheme. None of these steps uses numerical torsion counts or
density, and their Lean proof remains a separate contribution.

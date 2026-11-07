# The negative Borel cell of a supplied split pinning

This is an internal supporting module for the proof of
`SplitDominantHighestWeightRepresentationsExistStatement`. It packages the
Library's dynamic subgroups, big-cell and socle results for a supplied
`p : SplitPinning G` into one negative Borel subgroup, one positive unipotent
subgroup, one big-cell coordinate and one shared "realized weight" predicate.
The surrounding mathematics is the classification of simple representations by
highest weight (Milne, *Algebraic groups*, 2017, Chapter 22), but no
declaration here formalizes a specific literature statement. Every result is
derived from Library theorems named below.

Throughout, `k : Type u` is a field, `G` is a group scheme over
`Spec (CommRingCat.of k)` with `[IsAffineHom G.X.hom]`, and `p : SplitPinning G`
supplies a connected reductive structure, a split maximal torus
`p.inclusion : p.torus.toGrp ⟶ G`, its root datum and a base `p.base`.

## A cocharacter positive on the base

`linearIndependent_toRat_simpleRoot`: the simple roots of `p.base` stay linearly
independent after `toRat`, by localizing the integral independence
`p.base.linearIndepOn_root`.

`exists_cocharacter_pairing_eq_height`: there are an integer `d > 0` and a
cocharacter `ν` of `p.torus` with
`latticePairing p.torus (p.rootDatum.root i) ν = d * p.base.height i` for every
root index `i`. The Library's `IsSplitTorus.exists_scaled_pairings`, applied to
the simple roots with target value `1` on each, gives `d` and `ν` with pairing
`d` on every simple root. Writing a root as an integral combination of simple
roots (`RootPairing.Base.exists_root_eq_sum_int`) and using
`RootPairing.Base.height_eq_sum` gives the formula. No coroot span or
semisimplicity hypothesis is used.

`positiveCocharacter` and `positiveScale` are chosen witnesses `ν` and `d`;
`positiveScale_pos` and `latticePairing_root_positiveCocharacter` record their
property. Consequently
`latticePairing_root_positiveCocharacter_pos_iff` says the pairing with a root
is positive exactly when the root is positive for `p.base`, and
`latticePairing_root_positiveCocharacter_ne_zero` says it never vanishes, since
heights of roots are nonzero. Hence
`isGenericCocharacter_positiveCocharacter`: `ν` is a generic cocharacter for
`p.inclusion` (each root of the torus is a `p.rootDatum.root i` by the range
clause of `p.isRootDatum`).

## The negative Borel and positive unipotent subgroups

`positiveGm` is `ν` as a homomorphism `𝔾_m ⟶ G`, the composite of
`CommGroupScheme.groupHom ν` with `p.inclusion`.

`centralizer_positiveGm`: the dynamic centralizer of `positiveGm` is the range of
`p.inclusion`. This combines the Library's generic-centralizer theorem
`genericCentralizer` (for the maximal split torus) with
`maximalTorusCentralizer`. `isRepresentedBy_centralizer_opposite` restates it
for the reversed cocharacter `Dynamic.oppositeCocharacter positiveGm` (`ν⁻¹`),
whose centralizer is the same, with `p.inclusion` as representing closed
immersion.

`negativeBorel` is the affine group scheme
`Dynamic.Affine.parabolicScheme ν⁻¹` representing the dynamic parabolic
`P_G(ν⁻¹)`, and `negativeBorelHom` its inclusion into `G`.
`positiveUnipotent` is `Dynamic.Affine.unipotentScheme positiveGm`
representing `U_G(ν)`, and `positiveUnipotentHom` its inclusion. Both
inclusions are closed subgroups, so their structure morphisms are affine
(`isAffineHom_negativeBorel`, `isAffineHom_positiveUnipotent`). The names
reflect the root signs: by the pairing formula, the roots on `U_G(ν)` are the
positive roots of `p.base`, and `P_G(ν⁻¹)` is the Borel subgroup of the negative
roots. This module proves no statement about those root sets; the names are
descriptive only.

`isUnipotent_positiveUnipotent`: `positiveUnipotent` is unipotent, by
`Dynamic.isUnipotent_of_isRepresentedBy_unipotent` for the smooth group `G` and
the closed representative.

`negativeBorelToTorus` is the dynamic limit homomorphism
`Dynamic.limitGroupHom` from `P_G(ν⁻¹)` onto its centralizer `p.torus`, and
`torusToNegativeBorel` the inclusion `Dynamic.centralizerToParabolic` of the
torus. `torusToNegativeBorel_comp` (its composite with `negativeBorelHom` is
`p.inclusion`) and `torusToNegativeBorel_comp_negativeBorelToTorus` (the
composite through the limit map is the identity) come from the corresponding
Library lemmas.

## Characters of the negative Borel subgroup

`borelCharacter lam` is the rational character of `negativeBorel` obtained from
a torus character `lam : characterLattice p.torus` by
`rationalCharacters.equivCharacterLattice` and restriction along
`negativeBorelToTorus`; it is additive (`borelCharacter_add`).
`borelCharacterCoordinate lam` is its coordinate function
`AffineCoordinates.characterCoordinate`. On every test point it evaluates to the
character value (`pointAlgebraHom_borelCharacterCoordinate`), is multiplicative
in `lam` (`pointAlgebraHom_borelCharacterCoordinate_add`) and is `1` at
`lam = 0` (`pointAlgebraHom_borelCharacterCoordinate_zero`).

`characterRestrict_torusToNegativeBorel_borelCharacter`: restricting
`borelCharacter lam` to the torus gives back `lam`.
`eq_borelCharacter`: every rational character `χ` of `negativeBorel` equals
`borelCharacter` of its torus restriction. This is the left-inverse property of
the Library's `Dynamic.parabolicCharacterEquiv` for the closed parabolic
`P_G(ν⁻¹)` with centralizer `p.torus`. It lets results stated with an arbitrary
character of the negative Borel subgroup be converted to the fixed form
`borelCharacter lam`.

## The big cell

`isOpenImmersion_cellMultiplication`: the multiplication
`U_G(ν) × P_G(ν⁻¹) ⟶ G`, `(u, b) ↦ u b`
(`SubgroupFunctor.cellMultiplication positiveUnipotentHom negativeBorelHom`), is
an open immersion. This is the Library's `oppositeCellStatement` for the
cocharacter `ν⁻¹`, using `(ν⁻¹)⁻¹ = ν`.

`exists_cellCoordinate`: there is a coordinate `q` of `G` that is a nonzerodivisor
of the coordinate algebra such that, on every test scheme `T` over
`Spec (CommRingCat.of k)` and every `g : T ⟶ G.X` at which `q` evaluates to a
unit, there are `a : T ⟶ negativeBorel.X` and `u : T ⟶ positiveUnipotent.X` with
`g = i(a) * j(u)`, where `i = negativeBorelHom` and `j = positiveUnipotentHom`.
The proof takes the identity point `x` of `G`, which lies in the open image of
the cell multiplication (it is the product of two identity points), and chooses
a global function `f` with `x ∈ D(f) ⊆` the image
(`IsAffineOpen.exists_basicOpen_le` for the affine scheme `G.X.left`). Then `q` is
the antipode of the coordinate of `f`. At the identity point, `q` is a unit
because the identity lands in `D(f)`, so `q ≠ 0`; the coordinate algebra is a domain for a
connected reductive group (`AffineCoordinates.isDomain_of_isConnectedReductive`),
so `q` is a nonzerodivisor. If `q` is a unit at `g`, then `f` is a unit at `g⁻¹`,
so `g⁻¹` lands in `D(f)` and factors as `u' b'` through the cell
(`SubgroupFunctor.exists_cell_factors_of_range_subset`). Inverting gives
`g = b'⁻¹ u'⁻¹`, with `b'⁻¹` in the negative Borel subgroup and `u'⁻¹` in the
positive unipotent subgroup. The test schemes carry no affineness or
reducedness restriction.

`cellCoordinate` is a chosen such `q`, with
`cellCoordinate_mem_nonZeroDivisors` and
`exists_factors_of_isUnit_cellCoordinate`. This is exactly the shape of the cell
hypotheses of `Chevalley.affineCovariantSocleRepresentation_isIrreducible`.

## Realized weights

`IsRealizedBy lam f` for a torus character `lam` and a coordinate `f` of `G` is
the conjunction of three conditions:

1. `f` is in `AffineCoordinates.leftCovariantSubspace negativeBorelHom
   (borelCharacterCoordinate lam)`: left translation by the negative Borel
   subgroup multiplies `f` by the extended character of `lam`;
2. `f` is in `AffineCoordinates.rightInvariantSubspace positiveUnipotentHom`:
   `f` is invariant under right translation by `U_G(ν)` on every test;
3. the counit of `f` is `1`, that is, `f(1) = 1`.

`IsRealizedWeight lam` means some coordinate realizes `lam`. These are the
interface predicates shared by the parts of the final proof. They are internal
definitions, not literature notions. On points, condition 1 reads
`f(b g) = lam(b) f(g)` for `b` in the negative Borel subgroup.

`isRealizedBy_zero` and `isRealizedWeight_zero`: the constant coordinate `1`
realizes `0`. `IsRealizedBy.mul`: if `f` realizes `lam` and `f'` realizes `mu`,
then `f * f'` realizes `lam + mu`. The covariance is checked pointwise with
`AffineCoordinates.mem_leftCovariantSubspace_iff_points` and the
multiplicativity of the character coordinate; invariance and the counit are
multiplicative. Consequently `IsRealizedWeight.add` (the realized weights are
closed under addition) and `IsRealizedBy.pow` (`f ^ n` realizes `n • lam`).

`IsRealizedBy.isIrreducible`: if `f` realizes `lam`, then the finite covariant
socle representation `Chevalley.affineCovariantSocleRepresentation G f` is
irreducible in the Library's all-affine-test sense. This applies
`Chevalley.affineCovariantSocleRepresentation_isIrreducible` with
`i = negativeBorelHom`, `j = positiveUnipotentHom`, the unipotence of
`positiveUnipotent`, `χ = borelCharacterCoordinate lam`, `q = cellCoordinate`
and its cell property, and the three conditions of `IsRealizedBy`.

## Scope

The module identifies no highest weight of the socle representation, proves no
statement about which weights are realized, and assumes neither algebraic
closedness nor any characteristic. Those are separate parts of the final proof.

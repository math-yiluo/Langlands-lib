# Replacing ordered orbit representatives

This internal construction connects the published actual orbit sets in the left
quotient `P \ G` to Mathlib's double-coset quotient. It then replaces the
representatives of an already supplied ordered orbit decomposition while
preserving the orbit sets and their order. Its provenance is elementary group
quotient reasoning from the existing definitions in
`ClosedSubgroupDefinitions` and `WeylDefinitions`, together with Mathlib's
`DoubleCoset.eq`; it does not assert an additional result from the literature.

## Orbit membership and quotient classes

For subgroups `P` and `Q` of a group `G`, the existing convention is
`cosetOrbit P Q w = {P w⁻¹ q | q ∈ Q}`.
The theorem `quotientMap_mem_cosetOrbit_iff` proves that the image of `x` in
`P \ G` belongs to this set exactly when
`DoubleCoset.mk P Q w⁻¹ = DoubleCoset.mk P Q x`.
An orbit witness gives equality in the left quotient, hence
`x * (w⁻¹ * q)⁻¹ ∈ P`; this supplies the left factor in the double-coset
criterion. Conversely, a factorization `x = p * w⁻¹ * q` gives the orbit
witness using the right-quotient relation.

`cosetOrbit_eq_iff_doubleCoset_eq` identifies equality of these actual orbit
sets with equality of the corresponding double-coset classes. One direction
tests the point represented by `v⁻¹`; the other applies the membership
criterion after quotient induction. Both membership and equality lemmas are
pure group-theoretic: no topological hypotheses occur in their types.

## Replacing an ordered decomposition

Given `s : OrderedDoubleCosets P Q m`, `s.doubleCosetEquiv` is an equivalence
from `Fin m` to the actual double-coset quotient, sending `i` to the class of
`(s.representative i)⁻¹`. Injectivity follows from pairwise disjointness: equal
classes give equal nonempty orbit sets. Surjectivity follows by applying the
cover property to a representative in the left quotient.
`doubleCosetEquiv_apply` records the defining formula.

`s.replaceRepresentatives r h` accepts elements `r i` whose inverse classes
equal the corresponding inverse classes of `s.representative i`. Equality of
orbit sets transfers the cover, pairwise disjointness, and openness of every
initial union. Thus the new structure uses exactly `r` as its representative
function and retains the same ordered orbit subsets.

`s.classifiedRepresentatives r h` accepts any type `A`, independently of the
universe of `G`, and a function `r : A → G` for which the inverse
double-coset-class map is bijective. Composing `s.doubleCosetEquiv` with the
inverse classification equivalence yields `e : Fin m ≃ A`.
The result includes this equivalence and a replacement ordered decomposition
whose representative at `i` is exactly `r (e i)`.

## General linear specialization and scope

For a topological commutative ring `F`, block shapes `B` and `C`, an existing
ordered decomposition for their actual parabolic subgroups, and bijectivity of
the published `parabolicDoubleCoset F B C`, `minimalPermutationOrdering`
returns an equivalence with `MinimalRepresentatives B C` and an ordered
decomposition represented by the corresponding permutation matrices.
The inverse convention agrees definitionally with `parabolicDoubleCoset`.
The rank is arbitrary, including zero; bijectivity is an explicit assumption
at this generality, not a theorem for arbitrary rings.

No existence of an ordered decomposition or Bruhat classification is proved
here. In particular, the module makes no claim of a geometric graded-piece
isomorphism, modulus cancellation, or the normalized p-adic geometric lemma.

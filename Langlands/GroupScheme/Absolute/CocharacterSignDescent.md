# Descent of a Galois-stable pairing-sign class

Worker 1272.

This internal construction derives an alternative interface for the published
integral Galois averaging and actual cocharacter descent results. It uses the
published `HaveSamePairingSigns` predicate on actual characters and cocharacters.
No additional theorem from the literature is asserted.

Let `k` and `K` be commutative rings in an arbitrary common universe, with a
`k`-algebra structure on the integral domain `K`. Let `T` be a commutative group
scheme over `Spec k`, `ν` an actual cocharacter of `T_K`, and `Φ` an arbitrary
set of actual characters of `T_K`. Equip `Aut_k(K)` with a finite enumeration.
Assume that every Galois translate of `ν` has the same nonnegative, zero and
strictly positive pairing signs as `ν` at each character in `Φ`.

The theorem `galoisOrbitSum_signs_of_orbit_signs` proves that the integral
Galois orbit sum also has those signs on `Φ`. For a fixed character, the proof
applies the published `nonneg_orbitSum_iff` to its integer-valued additive
pairing map. It applies that result again to the negative of the pairing map:
equivalence of strict positivity for every translate gives equivalence of
nonpositivity by logical negation. The resulting nonnegative and nonpositive
comparisons determine zero by antisymmetry and strict positivity by negation.
The zero comparison in the orbit hypothesis is consequently redundant, but
retaining `HaveSamePairingSigns` gives a uniform interface.

Now suppose `k` and `K` are fields, `K/k` is finite dimensional and Galois,
and `T` is affine. Under the same orbit-sign hypothesis,
`descendedOrbitSum_signs_of_orbit_signs` proves that the base change of the
published actual `descendedOrbitSum` has the original signs on `Φ`. Its proof
rewrites the published exact base-change recovery equality and applies the
preceding theorem.

The definition `descendedSignRepresentative` returns this descended orbit sum
as an actual cocharacter over `k`, together with the proof that its base change
has the prescribed signs. It neither selects nor assumes an already descended
representative: its value is the existing integral orbit-sum descent.

There is no negation-closure or Galois-stability assumption on `Φ` in this
interface. Its explicit orbit-sign premise is a different input from the
family-stability, cone-stability and negation-closure inputs of
`CocharacterAveragingSigns`; no equivalence of those sets of inputs is claimed.
The family may be empty, and the integral sum uses no division or restriction
on characteristic. Applications must still prove the orbit-sign premise for
their actual family. This module proves no root geometry, equality of dynamic
subgroup functors or parabolic classification.

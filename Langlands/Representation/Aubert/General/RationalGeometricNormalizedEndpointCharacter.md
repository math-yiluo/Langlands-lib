# Actual normalized endpoint half-characters

This internal prerequisite identifies the remaining endpoint ratio with the
original inside source Jacquet inverse half-character and target induction
positive half-character. It then gives the exact original normalized compact
coefficient on the entire target intersection, retaining both epsilon corrections.
It does not prove the host exact-K0 expansion.

## Literal intersections and conventions

For subgroups `MI`, `MJ`, `UI`, `UJ` of the original group and an element `n`, set
`Ls0 = MJ ∩ n⁻¹ MI n`, `S0 = MJ ∩ n⁻¹ UI n`,
`Lt0 = MI ∩ n MJ n⁻¹`, and `R0 = MI ∩ n UJ n⁻¹`.
The Lean definitions use the published `geometricSourceIntersection` and
`geometricTargetIntersection`. All inside copies are literal `subgroupOf`
subgroups: `Ls = Ls0.subgroupOf MJ` and `Lt = Lt0.subgroupOf MI`.
The published equivalence `e : Lt ≃* Ls` sends the ambient point `l` to
`n⁻¹ l n`; no representative or subgroup is replaced.

`geometricSourceEndpointInverseHalfCharacter` is the canonical closed Haar
inverse half-character of `S0.subgroupOf MJ`, on `Ls`, with the supplied actual
normalizer witness. `geometricTargetEndpointHalfCharacter` is the canonical
positive half-character of `R0.subgroupOf MI`, on `Lt`. Closedness of `MJ` and
`MI` supplies the local compactness instances of the respective ambient groups.

## Source and target comparison proofs

`geometricSourceEndpointInverseHalfCharacter_transport` first applies
`closedInverseHalfCharacter_subgroupOf` to flatten the nested source subgroup.
The explicit equality of flattened `e(l)` with `conjugationEquiv n` at flattened
`l` preserves the inverse-conjugation convention. The published
`closedInverseHalfCharacter_conj` then identifies the value with the inverse
half of the actual forward source-endpoint intersection modulus
`delta_a = geometricCommonLeviIntersectionModulus ... UI MJ ...`.
The proof finishes by unfolding that modulus, for every `l : Lt`.

`geometricTargetEndpointHalfCharacter_eq` applies
`closedHalfCharacter_subgroupOf` to the target endpoint. It identifies the actual
inside half-character with the complex positive half of the literal modulus
`delta_b = geometricCommonLeviIntersectionModulus ... MI UJ ...` on all of `Lt`.
These generic comparisons require a locally compact topological group, the
stated subgroup closedness and normalization witnesses; they assume no relation
between distinct radical moduli.

## Full target intersection

In the rational-point specialization, `hSource` and `hTarget` are the actual
source and target semidirect decompositions. Put
`K = (MI ∩ n PJ n⁻¹).subgroupOf MI` and
`Rt = (MI ∩ n UJ n⁻¹).subgroupOf MI`. Write `pi` for
`hTarget.projection : K →* Lt` and `p = e.comp pi` for the original coefficient
Levi map. The theorem
`geometricNormalizedCompactEndpointRatioCharacter_eq_endpoints` substitutes
the two generic comparisons into the existing endpoint-ratio definition,
giving exactly `endpointRatio = targetHalf * sourceInverseHalf.comp e`.

`geometricNormalizedCompactEndpointCharacter` is a character on the entire `K`.
It is the original inside positive induction half-character of `Rt` on `K`,
multiplied by the original source inverse half-character pulled back through
`p`. Its target half is taken on the whole parabolic intersection, as required
by normalized induction, before any inflation is inferred.

Assume the original `UJ` is a limit of compact subgroups. The imported
`isLimitOfCompactSubgroups_geometricTargetRadical` transfers this property to
`Rt`, using forward conjugation and closed intersection. The published
`isUnimodularModulus_of_isLimitOfCompactSubgroups` therefore gives its
unimodularity. Applying `closedHalfCharacter_eq_comp_projection` to `hTarget`
identifies the whole target half with inflation of its actual Levi half.
Together with `p = e.comp pi`, this proves
`geometricNormalizedCompactEndpointRatioCharacter_inflate`:
`endpointRatio.comp pi = geometricNormalizedCompactEndpointCharacter`.

Finally `geometricNormalizedCompactCharacter_eq_epsilonEndpoints` substitutes
this identity into the original full-intersection coefficient inflation theorem.
It proves, as an equality of monoid homomorphisms on every `x : K`,

`eta = (epsilonOne * epsilonTwo).comp pi * geometricNormalizedCompactEndpointCharacter`.

Both original epsilon corrections remain. The proof uses multiplication and
composition of the actual characters and assumes no balance identity.

## Hypotheses and retained obligations

The rational-point results retain an arbitrary field, the actual torus morphism
and cocharacter, arbitrary `I` and `J`, and the given point-normalizer element.
They use the original two parabolic semidirect decompositions, both actual
geometric endpoint decompositions, the locally compact nonarchimedean point
group and closed original radicals and Levis. Inflation also requires the stated
compact-limit property of `UJ`. The final coefficient identity retains
`StandardCocharacterStatement`, connected reductivity, maximal split torus,
generic cocharacter, point-normalizer comparison, second countability, closed
original parabolics and continuity of both original Levi projections. It imposes
no splitness, characteristic-zero or minimal-representative restriction. These
are character-level results; no representation-carrier universe is specialized.

The provenance is internal: the construction and proofs combine the published
subgroup-of modulus, conjugation, endpoint-ratio, compact-limit unimodularity and
full-intersection inflation results. No new external source theorem is asserted.
The unchanged Character and Inflation pairs are included as helpers while their
publication is pending at this workspace base. Whole-common-Levi distinct-radical
balance, its consequence for both epsilons, the normalized representation and
functor identifications, compact/full induction, proper graded comparison,
ordered filtration and the exact normalized K0 sum remain separate obligations.

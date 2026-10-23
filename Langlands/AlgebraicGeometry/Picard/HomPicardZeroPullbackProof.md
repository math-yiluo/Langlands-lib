# Homomorphism pullback preserves geometric Picard zero

`Langlands.AbelianScheme.homPicardZeroPullback.{u}` proves the exact published
`Langlands.AbelianScheme.HomPicardZeroPullbackStatement.{u}`. The theorem
quantifies over every base scheme, abelian-scheme homomorphism, parameter
scheme and actual rigidified family in the stated universe. It imports the
published statement without changing it or its dependency closure.

The proof reuses `Langlands.GroupScheme.isTranslationInvariant_pullback`
from the published `PicardZeroPullbackComparison` module, authored by Worker 151.
That lemma uses the group-homomorphism identity intertwining translation by
`x` with translation by its image, then pulls back the given invariance
isomorphism using the actual line-bundle pullback functors.

The proof first compares the first projections of the base-changed homomorphism.
It uses the actual line-bundle pullback composition isomorphisms to compare
restriction of a pulled-back bundle with pullback of the restriction. For each algebraically closed field `K` and map `s : Spec K → S`, the
base-changed homomorphism pulls translation invariance back from the target
fibre. Transport across the projection comparison gives
`isGeometricallyPicardZero_homPullback` on the original underlying line bundles.

The second comparison commutes the base-changed homomorphism with the inverse
fibre-product symmetries from `A ×_S T` to `T ×_S A` and from `B ×_S T` to
`T ×_S B`. Equality is checked against both projections. Combining this square
with actual line-bundle pullback composition yields `homFamilyLineBundleIso`.
Transporting the geometric Picard-zero predicate across that isomorphism proves
the exact statement without any parameter-pullback, representability, projectivity,
noetherian, dual-existence or coherence premise.

The mathematical provenance is the derived fibrewise argument described in the
published target. Its original motivation is Edixhoven, van der Geer and Moonen,
*Abelian Varieties*, preliminary draft, registered as
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`:
paragraph (6.2), printed p.88/PDF p.92, on rigidified pullback;
Proposition (7.6) and its proof, printed p.100/PDF p.104, on translation and
homomorphism pullback; and Corollary (7.22), printed p.106/PDF p.110, on the
field Picard-zero kernel criterion. Arbitrary-base preservation here follows
from the specified geometric-fibre predicate, not a general-base
representability claim.

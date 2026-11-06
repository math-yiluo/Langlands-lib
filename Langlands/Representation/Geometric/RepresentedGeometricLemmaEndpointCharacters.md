# Actual inner endpoint characters of represented intersections

This internal adapter identifies the original inner Jacquet and induction
half-characters with the literal endpoint characters of a represented
geometric-lemma datum `D`. Its provenance is functoriality and injectivity of
the original Levi point maps, the published Haar transport under an ambient
continuous group equivalence, and the datum's actual intersection identities.
It is derived content rather than a new assertion from the literature.

Use the generic orientation `MI = L(k)`, `MJ = M(k)`, `UI = U(k)`,
`UJ = N(k)` for the original ambient point images, and `n = z⁻¹`. The
source common Levi is `M(k) ∩ z L(k) z⁻¹`, retained as a subgroup of
`M(k)`. `sourceCommonLeviPointsEquiv` identifies this subgroup with the
original represented `M'(k)` and its Levi point topology. Its underlying
map is the original composite inclusion. The theorem
`intersectionSubgroupEquiv_commonLevi` identifies the generic conjugation
with `D.e`; both act by `x ↦ z x z⁻¹` on ambient points.

The two normalization lemmas follow from the datum's actual source and
target semidirect decompositions. `mem_pointImage_leviPointsEquiv` checks
subgroup membership before and after the original Levi point equivalence:
the forward direction uses point-map functoriality, and the reverse
direction uses injectivity of that equivalence.

`sourceInverseHalfCharacter_endpoint` transports the Haar character of
the actual inner source radical through the original source Levi point
homeomorphism. The radical and common-Levi membership equivalences follow
from `D.sourceRadicalPoints_eq` and `D.sourceLeviPoints_eq`. This identifies
the actual source Jacquet inverse half with the generic source endpoint
inverse half pulled back to `M'(k)`. The theorem
`sourceInverseHalfCharacter_commonLevi` then composes with the actual
`D.e` and applies the published generic conjugation transport. The result
is the inverse half of the forward source-endpoint intersection modulus
on all of the actual target common Levi `L'(k)`.

`targetHalfCharacter_endpoint` uses the target Levi point homeomorphism
and `D.targetRadicalPoints_eq` and `D.targetLeviPoints_eq` in the same
way. It identifies the actual inner target induction positive half with
the generic target endpoint half pulled back to `L'(k)`. The theorem
`targetHalfCharacter_commonLevi` applies the published generic ambient
subgroup comparison to express this as the positive half of the literal
target-endpoint intersection modulus.

The ambient group has the canonical rational-point topology and is locally
compact and nonarchimedean over a Hausdorff topological field; its scheme
is affine. Inner ambient point topologies and local compactness are
transported through the original Levi maps. No root presentation,
standardness, representation finiteness, or modulus-balance premise is
added. The two endpoint radical moduli remain distinct. The five-subgroup
cancellation and the final natural orbit comparison remain separate
obligations.

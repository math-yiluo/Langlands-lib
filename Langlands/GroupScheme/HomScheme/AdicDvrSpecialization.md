# Algebraization on completed DVR specializations

Consider a compatible adic homomorphism system over a
Noetherian local ring with diagonalizable source. Assume that its target
is smooth, separated and quasi-compact with affine actual residue
fibres. For every nonclosed point of the base,
`CompletedDvrSpecializationEffectivityStatement` gives a complete adic
test reaching that point on which the transported system is the
restriction of an actual group-scheme homomorphism.

The proof chooses a DVR specialization from the given point to the
closed point. The ring map carries the maximal ideal of the base
inside the maximal ideal of the DVR. The actual pullback of the
target to the DVR is affine by `isAffineHom_dvrPullback_of_residueFibers`.
Pulling back to the completion at the extended ideal preserves
affineness. The affine-target
adic comparison for a diagonalizable source then algebraizes the
system pulled back by the Library's extended-ideal `System.pull`.
Faithful flatness of the completion ensures that a
point of the completed test maps to the generic endpoint of the DVR and
hence to the given point.

This is an internal form of the valuation comparison used in SGA 3,
Exposé XV, proof of Theorem 4.1, parts b) and c), recomposed pp. 261–264,
registered `sga3-expose-xv-raynaud-2008`. Here the original ambient
is smooth with affine residue fibres, so the Library's DVR affineness
theorem supplies the affine target before completion. The proposition
is about algebraization on the completed valuation tests.

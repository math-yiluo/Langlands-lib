# Full residue centralizers in actual neutral comparison images

This internal adapter uses arbitrary universe `u`, the actual inertia fixed
field of a nonarchimedean local field and its integer ring. Its inputs are
building data `C`, two supplied relative-component models `M`, `M'`, and
apartment subsets `Ω`, `Ω'`. Each full model's integral points are the
character-valuation kernel intersected with the pointwise fixer of the
corresponding apartment image. The supplied comparison `ψ` goes from
`M'.neutral` to `M.neutral` and has generic map the identity. Only the target
subset `Ω` is required to be nonempty; no incidence or boundedness hypothesis
is needed.

The target centralizer is the existing
`unramifiedNeutralCentralizerModel C M Ω hM`. It is the actual smooth
closed centralizer of `unramifiedNeutralSplitTorusData C M Ω hM` inside the
target neutral model, with prescribed generic group `C.centralizer.Z` and
generic inclusion `C.centralizer.j`.

`unramifiedNeutralCentralizerLift` applies the proved strictly Henselian
smooth homomorphism extension theorem. The target centralizer model is
smooth, and `unramifiedNeutralCentralizerModel_integralPoints_le` puts its
integral points in the source neutral-centralizer integral subgroup. The
source centralizer's compatible map then puts their ambient images in the
source neutral model. Thus the extension has exactly the prescribed generic
centralizer map.

Generic rigidity identifies the lift followed by `ψ` with the original
target centralizer inclusion. The same identity holds after residue base
change. `unramifiedNeutralCentralizerImageFactor` composes the residue lift
with the schematic-image projection of `ψ`; composing this factor with the
image inclusion recovers the target centralizer residue map.

The existing
`IntegralSplitTorusData.centralizerModelMap_specialFibre_isCentralizer`
identifies the range of that map with the full centralizer of the actual
residue torus, on every scheme test. It follows from base change of the
integral centralizer's representability and `torusCentralizer_baseChange`.
The factor therefore proves
`unramifiedNeutral_specialCentralizer_le_image`: containment of that entire
centralizer subgroup functor in the actual neutral comparison image.

The provenance is internal composition of the published neutral-centralizer
comparison, smooth extension, generic rigidity and residue centralizer
representability. This adapts the zero-fixer centralizer-image construction
to supplied actual neutral components without a global identification of
neutral integral points with a chosen zero subgroup. Model existence,
full unipotent-radical containment, congruence-kernel containment,
parabolicity and the opposite-factor conclusion remain further obligations.

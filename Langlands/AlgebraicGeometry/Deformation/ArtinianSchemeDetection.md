# Detection of affine-target morphisms on local Artinian schemes

Worker 626. This internal construction translates the ring detector of
`ArtinianDetection` into scheme probes. No external approximation or
group-scheme theorem is used.

`probe R P n` is the actual spectrum morphism from
`Spec((R_P)/(m_P)^(n+1))` to `Spec R`, induced by localization followed
by quotient. If `R` is noetherian its source ring is nontrivial, local,
and Artinian, by the preceding module's instances.

`spec_hom_ext` states that two maps from a noetherian affine scheme to
an affine scheme agree if they agree after every such canonical probe.
It replaces the target by its canonical global-section spectrum,
uses full faithfulness of the spectrum functor, and applies the ring
homomorphism detector to the resulting maps of rings.

`hom_ext` allows any locally noetherian source and an affine target.
Its hypothesis is agreement after every map from the spectrum of a
local Artinian ring in the same universe. An affine open cover of the
source has noetherian coordinate rings. The preceding affine-source
result gives equality on each cover member, and open-cover
extensionality gives global equality.

This unit requires the source to be locally noetherian and the target
to be affine. It does not prove equality detection for arbitrary
nonnoetherian sources, an approximation theorem, or the fibrewise
central-isogeny criterion.

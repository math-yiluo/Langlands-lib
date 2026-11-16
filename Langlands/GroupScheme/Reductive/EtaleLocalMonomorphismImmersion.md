# A reductive immersion criterion from closed split torus images

This internal reduction removes the global splitting assumption from the
conditional reductive immersion criterion. Its source is an arbitrary
reductive group scheme over an arbitrary scheme, and its target is a smooth
affine group scheme over that base. The underlying morphism is assumed monic.
The conclusion is immersion.

`ClosedSplitTorusImagesAfterEtaleBaseChange` is the remaining hypothesis:
after every affine étale base change, the composite of every closed
coordinate split torus inclusion into the source with the homomorphism into
the target is a closed subgroup. This hypothesis is explicit. The module
does not establish unconditional torus image closedness or conclude closed
immersion of the original homomorphism.

The helper `BaseImmersion.of_etale_base_neighbourhoods` proves that immersion
of an arbitrary morphism over a base can be checked on étale neighbourhoods of
all base points. It pulls such a neighbourhood to the target; the pullback
range formula shows that its image contains the given target point. The
underlying base change square transfers the immersion hypothesis to the
canonical target pullback. The étale target neighbourhood criterion then
applies.

For a reductive source, the proof chooses an affine étale splitting
neighbourhood at each base point. This supplies a closed coordinate split
maximal torus and a common full fibrewise root datum. Reductivity and the
target's smoothness and affineness persist under base change. The closed
split torus image hypothesis supplies exactly the remaining premise of the
split reductive immersion criterion. That criterion gives immersion on the
neighbourhood, and the helper descends it globally.

The provenance is internal composition of the Library's étale local reductive
splitting theorem, conditional split reductive immersion criterion, and
scheme immersion descent. No additional noetherian assumption or separate
external-source translation is asserted.

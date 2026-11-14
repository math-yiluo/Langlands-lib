# Etale conjugacy from presentations agreeing at a field point

This internal module extends the affine dynamic-conjugacy construction to
arbitrary base schemes. The ambient group is smooth and affine over the base.
Two actual subgroup homomorphisms have global dynamic presentations, and the
normalized presenting cocharacters agree at a supplied field-valued point.
The result is actual etale subgroup-conjugacy data at the image of that point.
No relative-parabolic hypothesis is needed for this conditional construction.

`EtaleSubgroupConjugacyData.comp` composes the projection of conjugacy data with
an etale base morphism. It transports the conjugating section through the
canonical isomorphism from iterated to direct pullback. Naturality of this
isomorphism, compatibility of inner conjugation with group homomorphisms, and
invariance of subgroup ranges under source isomorphisms give the direct-pullback
conjugacy equation.

`etaleConjugacyOfFieldPointPresentations` chooses an affine open chart containing
the image of the field point. Since the spectrum of a field has one point, the
given morphism factors through this chart. Both presentations pull back, and
the cocharacter tower comparison preserves equality at the lifted field point.
The residue-transporter construction reflects this equality to the chart's
canonical residue field and supplies the identity transporter. Smoothness and
affineness survive base change; the ambient group over the affine chart has
affine total space. The affine dynamic-conjugacy construction therefore
applies. Finally, the composition constructor returns conjugacy over the
original base with a point above the original field point's image.

The module is derived from the Library's affine open charts, pullback
comparisons, subgroup-range functoriality and the imported dynamic-conjugacy
and residue-transporter constructions. It introduces no new external
source assertion and does not itself prove the relative-parabolic target.

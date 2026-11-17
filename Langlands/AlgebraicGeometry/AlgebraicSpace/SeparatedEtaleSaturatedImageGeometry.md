# Scheme geometry of a compact separated etale saturation

This internal extension of `SaturatedLocalImageGeometry` replaces its structural
monomorphism by a closed diagonal and an etale chart composite. Its proposition
retains an actual compact scheme, a separated etale map to the affine base, a
represented pullback square and a locally surjective projection to the local
image. It does not assert that the local image is already represented.

The saturation is the sheafified image of the translated chart. Its source is
affine, as a fibre product of affine schemes. Its base morphism is etale by base
change. The represented-image geometry helper gives a separated etale map from
the chosen compact representative to the affine base. The remaining Yoneda and
subfunctor pullback construction is the published saturation argument: the image
inclusion identifies the represented square, and the original chart factors
through its projection, proving local surjectivity.

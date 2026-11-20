# Rational polarized frame actions

Harris (1997), Appendix, printed p. 113 (PDF p. 39), acts on
the rigidifying map by inverse precomposition. An element of
`RationalSimilitudeIso.Automorphism` is an actual invertible
order-linear section equipped with the two polarization identities.
The product \(gh\) acts on the frame by \(g\circ h\).

On an affine framed class with rigidification \(\rho\), the action of
\(g\) replaces \(\rho\) by \(\rho\circ g^{-1}\) after coefficient
extension of \(g^{-1}\). The identity and composite laws follow from
those of actual changes of frame. Naturality under affine test maps
gives `PolarizedFramedAffinePoint.frameActionHom`.

The split-special tangent conditions depend on the polarized target.
Since change of frame preserves that target, it restricts to natural
isomorphisms of split-special functors, including for two distinct
frames. `Harris.splitSpecialFrameActionHom` uses these isomorphisms for
a fixed frame, and the inclusion into the polarized affine functor
intertwines the natural actions.

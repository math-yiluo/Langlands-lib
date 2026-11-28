# Scheme maps from affine changes of coordinates

For an affine open \(W\) of \(X\) over \(\operatorname{Spec}R\),
`affineOpenEndomorphism` uses the canonical isomorphism
\(W\cong\operatorname{Spec}\Gamma(X,W)\) to turn an endomorphism of the
section \(R\)-algebra into a morphism of \(W\). Contravariance gives the
composition formula, and the identity map agrees with the identity of the
open scheme. A commutative restriction square on section algebras gives
the corresponding square with the open inclusion. The algebra structure
map identifies the result as a morphism over \(\operatorname{Spec}R\).

Let \(I\subseteq R\) be an ideal. If the section endomorphism is congruent
to the identity modulo \(I\Gamma(X,W)\), its composite with the section
reduction agrees with the section reduction. The proof uses the kernel
of the actual reduction map on the affine open. Applying the spectrum
functor yields agreement with the identity on the preimage of \(W\) in
the actual base change to \(R/I\). When \(I^2=0\), that preimage
surjects onto \(W\) on points. The endomorphism followed by the inclusion
therefore agrees pointwise with the inclusion, as required by
`TwistedOpenGluing.Data`.

These are consequences of the affine scheme and section-ring comparisons
for the actual open subschemes. The construction turns affine coordinate
changes into transition maps for gluing schemes.

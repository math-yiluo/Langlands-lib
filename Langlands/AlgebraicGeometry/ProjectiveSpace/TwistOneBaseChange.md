# Affine base change of the actual degree-one twist

For a commutative `A`-algebra `B`, `twistOneBaseChangeIso` identifies the
pullback of the Library's native `twistOne A m` along `baseChangeMap A B m`
with `twistOne B m`. The witness in `exists_twistOneBaseChangeIso` sends the
actual pullbacks of the coordinate sections to the corresponding sections
with the same labels. The proof uses the standard coordinate charts. Their
inverse images are the charts with the same labels, and the regular
functions `Xⱼ / Xᵢ` on these charts are preserved by the published
coefficient-extension formula for homogeneous fractions. Generation opens
and local coefficient relations therefore match, and the published
matching-sections theorem constructs the isomorphism.

`RelativeProjectiveSpace.polynomialIsoSpec_twistOneIso` applies this result
from `ULift ℤ` to `B`, since the relative twist is defined by pulling back
the integral twist and the integral projection of `polynomialIsoSpec` is
precisely scalar extension. This identifies the two actual twists across
the schemes' comparison isomorphism. There are no field or noetherian
assumptions and no asserted coherence for iterated scalar extensions.

The results are derived from the published projective base-change,
coordinate-chart, and module comparison theorems, using the degree-one
instance of the homogeneous dehomogenization formula.

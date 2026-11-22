# The degree-one uniformizer on compatible tangent vectors

Fix the embedded degree-\(d\) unramified coefficient field of a special atlas over an affine nilpotent test. Specify its residue embedding into \(\kappa\) and a residue coordinate \(\kappa \to B/\pi B\). The derivative of the full order action acts on the compatible tangent module, and the split coefficient projectors give its homogeneous components.

Take a division algebra unit \(\Pi\) with \(\Pi^d=\pi\) and the commutation relation for a field automorphism inducing arithmetic Frobenius on the residue field. With characters indexed by inverse Frobenius, the derivative of \(\Pi\) advances the compatible component by one. Evaluating in every universal chart localization identifies both projectors and the uniformizer derivative with those of the chart module. The chart degree condition then gives the degree condition for the overlap module, whose coordinates detect equality. `SpecialAtlas.tangentUniformizerStep` is the resulting linear map on each component.

This supplies the degree advance of the tangent operator in Drinfeld, *Coverings of p-adic symmetric regions* (1976), §2 B, printed p. 110 (PDF p. 4).

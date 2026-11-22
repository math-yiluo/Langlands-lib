# Naturality of the actual affine graded tangent pullback

Let \(Y\) and \(Z\) be special coordinate formal order modules on the same affine nilpotent test algebra with a common specified unramified coefficient field of reduced degree \(d\), residue embedding and residue coordinate. The split character grading comes from finite étale lifting and uses inverse Frobenius indexing. The given division uniformizer satisfies the power and arithmetic conjugation relations \(\Pi^d=\pi\) and \(\Pi a=\sigma(a)\Pi\).

`drinfeldTangentGradedPiSheafPulledMap` uses structural pullback on graded maps and identifies the pulled scalar with the scalar of the new test ring. Differentiating an order-linear formal isomorphism before this pullback or after coefficient extension gives a commutative square with `drinfeldTangentGradedPiSheafPullbackIso`. On total modules, mapping each linear coefficient by the ring homomorphism proves the derivative comparison on pure tensors. Naturality of the associated-sheaf pullback then proves the square on total sheaves. A homogeneous operator-compatible map is determined by its total map, so this is an equality of the graded sheaf morphisms.

The square gives the compatibility of the two affine tangent comparisons in Drinfeld, *Coverings of p-adic symmetric regions* (1976), §2 B and Proposition 2.4, printed pp. 110–111 (PDF pp. 4–5).

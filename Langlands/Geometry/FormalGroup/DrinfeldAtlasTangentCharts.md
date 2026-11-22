# Tangent line sheaves and transition maps on special formal atlas charts

Take an affine nilpotent test algebra with a special formal order atlas, a residue coordinate, and a residue embedding for its specified unramified coefficient field of reduced degree \(d\). The division uniformizer satisfies \(\Pi^d=\pi\) and \(\Pi a=\sigma(a)\Pi\), with \(\sigma\) inducing arithmetic Frobenius on the residue coefficients. The residue coordinate induces the split characters over every test algebra of the atlas by finite étale lifting, indexed by inverse Frobenius powers.

On a test algebra in a chart, `chartTangentLinePiSheaf` takes the graded tangent line sheaf of the actual coefficient-extended special coordinate law. On a test algebra in two charts, `chartTangentTransition` differentiates the full-order formal transition. The chosen coefficient grading and the operator of \(\Pi\) are preserved. The derivative respects formal identities and composition, and association of an affine sheaf respects the same equations. Applying these facts to the atlas identities gives the identity and cocycle on every common affine test algebra.

The construction supplies the chart transition data for the tangent sheaf in Drinfeld, *Coverings of p-adic symmetric regions* (1976), §2 B, printed p. 110 (PDF p. 4).

# Pullback of the tangent line datum of an actual special atlas chart

The affine base has a special formal order atlas, a residue coordinate, and a residue embedding for the atlas's unramified coefficient field of reduced degree \(d\). The split cyclic grading uses the inverse arithmetic Frobenius powers. The supplied uniformizer satisfies \(\Pi^d=\pi\) and \(\Pi a=\sigma(a)\Pi\), with \(\sigma\) arithmetic on the residue field.

`chartTangentPullbackIso` compares the pulled graded tangent sheaf of a chart with the graded tangent sheaf of the same chart on a new test algebra. The map of test algebras first gives the affine tangent pullback isomorphism. The full-order coefficient triangle identifies the extended chart with the chart on the target ring. The residue-coordinate comparison follows from compatibility of reduction with composition, and identifies the two character gradings used on the target.

This supplies the chart restriction map for the actual tangent part of Drinfeld's construction in *Coverings of p-adic symmetric regions* (1976), §2 B and Proposition 2.4, printed pp. 110–111 (PDF pp. 4–5).

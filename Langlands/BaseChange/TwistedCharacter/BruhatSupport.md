# Stability of double-coset support under twisted induction

The support filtration of a smooth induction has one step for each
initial union of the specified double cosets. A group automorphism that
preserves the inducing and restricting subgroups and fixes their chosen
double-coset representatives preserves each union. This follows by applying
the automorphism to the expression for a left coset in a right orbit.

`SmoothInductionSupportPreservation` expresses stability of the actual
subrepresentations of `rawSmoothSupportFiltration`. If the operator on
sections applies a linear map to the value of a section at the inverse
image of the argument, a nonzero transformed value implies a nonzero
original value at that inverse image. The stability of the orbit union
then gives stability of the support step. A linear map commuting with the
operators, such as the Jacquet quotient map for the descended operator,
takes each preserved step to a preserved image.

For relative parabolics in a standard block Levi of \(\mathrm{GL}_n\),
entrywise field automorphisms preserve both subgroups. Each permutation
matrix has entries zero or one, and injectivity of the block diagonal
embedding gives the same fixed-point property inside the Levi. The
evaluation formula for `relInducedSigmaIntertwiner` gives the support
identity for the relative induction operator.

This is the individual-orbit case of the stable support filtration in
Rogawski, *Trace Paley–Wiener theorem in the twisted case* (1988), proof of
Lemma 8.1, printed p. 222.

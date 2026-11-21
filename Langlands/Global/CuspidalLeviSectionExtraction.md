# Extraction from cuspidal Levi coefficient tensors

Consider a cyclic module for the concrete automorphic operators with a
simple quotient. The module has a linear tensor of cuspidal Levi
coefficients at the identity. Its translates obey finite parabolic
covariance, and their common kernel lies in the quotient kernel.
Each block coefficient space has an algebraic direct sum of actual
irreducible cuspidal summands.

Use the factor projections to obtain evaluations with coefficients in
one tuple of cuspidal summands. Restore the determinant characters
used to unitarize the blocks. The tensor product of the character twist
maps turns the finite covariance scalar into the action on the restored
blocks. The inverse half-modulus twist then gives normalized parabolic
covariance. Smoothness of the cyclic source makes each family of
evaluations an actual smooth section.

Each section kernel is stable under the full operator algebra. Upper
block annihilation passes through projection, and the block derivative
acts through the corresponding factor because its projection intertwines
that derivative. A scalar correction from the character twist also
vanishes in the kernel. Compact dual differentiation gives the remaining
Lie directions.

On a cyclic generator, the finite double cosets and the compact orbit
span bound the support of the section projections by a finite set.
The tuple coordinate maps separate the Levi coefficient tensors.
Consequently the common section kernel lies in the simple quotient
kernel. Cyclic projection extraction realizes the finite action of
the quotient as a subquotient of the normalized sections for one
tuple of actual cuspidal blocks.

This is the projection and induction step of Langlands, *On the notion
of an automorphic representation*, Corvallis Part I (1979),
Proposition 2, printed p. 205 (PDF p. 200). The implemented proof uses
algebraic coordinates of the cuspidal block spaces and finite support
on a cyclic generator. It takes the constant-term, character and
coefficient identities as hypotheses.

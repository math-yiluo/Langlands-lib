# Permutation of irreducible Hilbert summands by a twist

`HilbertSumTwistPermutationStatement` concerns a unitary action on a
complex Hilbert space with an orthogonal decomposition into nonzero
closed irreducible invariant subspaces. It assumes multiplicity one
in the form that any two such subspaces with equivariantly isometric
actions are equal. If \(U\) is a surjective linear isometry intertwining
the action with its pullback by a group automorphism, it induces a
permutation of the given summands.

The image of an irreducible invariant subspace under \(U\) is closed
and invariant. Pulling each closed invariant subspace of the image
back along \(U\) proves its irreducibility. The Hilbert-sum clause of
`unitarySchurHilbertSum` gives an equivariant isometric equivalence
from this image to a member of the decomposition. Multiplicity one
makes them the same subspace. Applying the same argument to \(U^{-1}\)
gives the inverse permutation.

`summandCompression_mul_twist_eq_zero` applies to a product \(AU\),
where \(A\) preserves every summand and \(U\) sends each summand to its
assigned image. The operator sends a moved summand into its distinct
orthogonal partner, so its compression to the original summand is zero.

Henniart–Lemaire, *Changement de base et induction automorphe pour GLₙ
en caractéristique non nulle* (2011), II.6.4, printed p. 120
(PDF p. 128), use multiplicity one and the covariance of the twist
to obtain the fixed cuspidal summands in the twisted trace.
The Lean module isolates the Hilbert space argument for this step.

Source ID `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`,
SHA-256 `7af2940c75a75937c1bf9096eb329931d4245cf592e3572db0ff93ec6e76c5e0`.

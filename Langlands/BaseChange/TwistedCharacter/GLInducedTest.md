# Twisted trace transfer for standard block parabolic induction

For a finite-order algebra automorphism of a local extension with its
module topology, the standard block parabolic satisfies the hypotheses
of `twistedInducedTest`. Its left quotient is compact, the parabolic is
closed and invariant under the entrywise action, and the open continuous
Levi projection intertwines the entrywise and blockwise actions.
`sigmaInducedTest` applies the common-test identity to this setup with
the supplied ambient measure and two-sided Levi Haar measure.

For normalized induction, the half modulus is an open-kernel character
on the Levi and is invariant under the automorphism. The twisting
operator therefore acts on sections by the same inverse change of
variable and inducing operator as for unnormalized induction. The
normalized covariance is implemented by absorbing the half modulus
into the inducing action. Its twisted distribution is the original
inducing distribution evaluated after multiplication of tests by that
character. Composing this operation with the unnormalized trace transfer
gives `sigmaNormalizedTraceTransfer`.

The section formula is the one in Henniart–Lemaire (2011), II.4.4,
p. 85, and Rogawski (1988), §3, p. 218. The proved transfer applies
to a supplied admissible Levi pair and its actual admissible induced
action, with independently quantified field and carrier universes.

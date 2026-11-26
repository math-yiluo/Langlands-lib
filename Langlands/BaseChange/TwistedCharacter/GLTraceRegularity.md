# Regularity of evaluation on induced σ-traces of the general linear group

`SigmaInducedTraceRegularityStatement` asserts the induced-family
regularity condition of twisted trace Paley–Wiener for the evaluation
functional of a test on `GL_n(E)`. The field `E` is nonarchimedean local,
and the field automorphism `σ` is continuous for the supplied module
topology and has a positive power equal to the identity. This is
condition (A)(ii) for a trace functional in Henniart–Lemaire (2011),
II.5.7, and the regularity check in Rogawski (1988), Lemma 11.1(a).

The proof transports the power identity through entrywise application
of the automorphism. It uses compactness of the quotient by the standard
parabolic, continuity of the Levi projection and admissibility of
inflation. The compact-quotient expansion from `InducedRegularity`
supplies the finitely supported coefficients on the Levi. Their support
and coefficient function witness `IsSigmaInducedRegularFunctional` for
the actual unnormalized induced σ-intertwiner.

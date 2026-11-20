# Character nonvanishing in a common Shintani fibre

`CommonShintaniLiftNonvanishingStatement` transfers a nonzero character value between two downstairs actions with the same irreducible admissible upstairs Shintani lift, at a regular semisimple element associated to an upstairs norm. The two lift identities may use independent intertwiners and constants.

Compose the two intertwiners with one inverse. Schur's lemma identifies the resulting endomorphism with a scalar, which is nonzero by invertibility. The local twisted character value scales by that same scalar. The two Shintani identities therefore give nonzero values for both downstairs actions at the supplied point.

`padicEssentiallySquareIntegrable_of_commonShintaniLift` specializes this comparison to a regular elliptic norm and a generic second action over a p-adic field. If that action failed essential square integrability, its elliptic character would vanish by the generic segment product argument. Uniqueness of the local character value gives a contradiction. The p-adic comparison expresses the conclusion in the square-integrability predicate used by the fibre statement.

This implements the deduction of essential square integrability in Henniart–Lemaire (2011), II.4.8, proof of the Lemme, printed p. 91. The proof assumes the two Shintani identities and a nonzero reference character value at the elliptic norm.

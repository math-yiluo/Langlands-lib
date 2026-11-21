# Hilbert globalization of real general linear GK modules

`realHilbertGlobalization` proves
`Langlands.Archimedean.RealHilbertGlobalizationStatement.{uV}` for every
positive size and every irreducible admissible real GK module in the stated
carrier universe. The proof uses the compact-picture Hilbert principal series
to construct the globalization. [Target statement](HilbertGlobalizationStatement.md)

Finite generation gives a finite-dimensional Jacquet quotient, and Jacquet
nonvanishing follows from the real principal-series subquotient theorem.
A nonzero real Jacquet functional supplies the Frobenius map into Haar
\(L^2\) on the orthogonal group. For an algebraic vector, the compact profile
of its orbit is real analytic near the identity by local Iwasawa
factorization. Evaluating its derivative at each compact group element gives
the Frobenius formula for the Lie derivative. Analyticity along each
exponential and the Cartan decomposition give invariance of the norm
closure. The restricted action is jointly continuous, and the induced map
into its smooth carrier intertwines the compact action and the genuine
derivative in every real matrix direction.
[Hilbert orbits](RealPrincipalSeriesFrobeniusHilbert.md),
[Invariant closure](RealPrincipalSeriesFrobeniusClosure.md),
[Smooth realization](RealPrincipalSeriesFrobeniusRealization.md)

Polynomial-weighted compact averages have finite rank in the ambient
principal series. Each such average of the closure lands in the algebraic
image by norm density and closedness within its finite-dimensional range.
Applying the polynomial integral test on a finite-dimensional orbit span
recovers every compact-finite vector. The injective Frobenius map therefore
identifies the algebraic module with the whole compact-finite subspace of
the smooth carrier. Compact admissibility follows by pulling back
finite-dimensional compact intertwiners. For topological irreducibility,
the preimage of a closed invariant Hilbert subspace is GK-stable by genuine
differentiation. Algebraic irreducibility and compact averaging then give the
two possible closed invariant subspaces. Smooth density uses the same
polynomial test on finite tuples of Lie-word derivatives. The smooth
averages exist because the full derivative-coordinate image is closed.
[Compact-finite recovery](RealFrobeniusCompactRecovery.md),
[Irreducibility and admissibility](RealFrobeniusHilbertAdmissibility.md),
[Smooth density](RealFrobeniusSmoothDensity.md)

The construction starts in `Type 0`. The proof transfers the Hilbert
structure and conjugates the action along the continuous linear equivalence
with `ULift.{uV}`. Transport also identifies the smooth carriers and their
compact-finite subspaces, preserving density and the two intertwining
identities. The general exponential-orbit theorem gives scalar
differentiability against every continuous complex linear functional on the
genuine word-derivative carrier by applying the functional to the limit in
that topology.
[Transport](SmoothHilbertTransport.md),
[Exponential differentiation](SmoothHilbertExponential.md)

Getz–Hahn, *An Introduction to Automorphic Representations* (2024),
§4.4, pp. 115–120, gives the context for Hilbert compact-finite vectors,
irreducibility and smooth globalization. The October 2026 errata, p. 1,
specifies continuity on finite-dimensional compact representations and
compact-finite recovery in the smooth carrier. The implemented proof
constructs the globalization directly using the Library's real Jacquet
Frobenius and compact-averaging results.

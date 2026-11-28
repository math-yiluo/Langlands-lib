# Convergence of nilpotent orbital integrals

`Langlands.HarmonicAnalysis.LieAlgebraNilpotentOrbitalConvergenceStatement` states that
every nilpotent element of a finite-dimensional semisimple algebra \(A\) over a
nonarchimedean local field \(F\) of characteristic zero has a quotient measure
giving absolutely convergent orbital integrals. The field and algebra universes
are independent. The algebra has its module topology, and the unit group has a
Borel measurable structure.

For each nilpotent \(N\), `UnitConjugation.HasConvergentNilpotentOrbitalMeasures`
asks for a Borel structure on the left coset space \(C\backslash A^\times\), where
\(C\) is the unit centralizer of \(N\). The witnesses include Haar measures on
\(A^\times\) and \(C\), with the latter also right invariant, and a measure \(\nu\)
on the coset space compatible with those Haar measures in the sense of
`QuotientIntegration.IsCompatible`. The condition `OrbitalIntegralConverges N ν`
requires \(Cg\mapsto f(g^{-1}Ng)\) to be \(\nu\)-integrable for every Schwartz–Bruhat
function \(f\) on \(A\). This gives the measure data used to define each nilpotent
orbital distribution in the spanning assertion of Harish-Chandra's Lemma 3.3.

Harish-Chandra's *Admissible invariant distributions on reductive p-adic groups*
(notes by DeBacker and Sally, AMS, 1999), §3.1, printed p. 17, asserts unimodularity
of the centralizer and invokes Deligne and Ranga Rao for convergence. Kottwitz's
*Harmonic analysis on reductive p-adic groups and Lie algebras* (2005), §3.3,
printed pp. 407–408, explains existence from unimodularity and the role of
nilpotent orbital integrals in Ranga Rao's convergence argument.

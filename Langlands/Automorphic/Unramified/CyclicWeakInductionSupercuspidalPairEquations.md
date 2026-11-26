# Unique-place supercuspidality from equal-rank pair equations

`CyclicWeakInductionSupercuspidalFromEqualSemilocalStatement` derives the unrestricted and totally complex unique-place supercuspidality propositions from the equal-rank semi-local Rankin–Selberg equation in the two field and presentation universes. It retains the four independent universes of the two propositions.

`cyclicWeakInductionSupercuspidalFromEqualSemilocal` constructs the twist functional-equation inputs for the downstairs self-pair and the upper orbit pairs, which all have equal rank. It uses `weakInductionOrbitBaseChange` to supply the cofinite upper orbit identity in `cyclicWeakInductionGammaOrderFromTwistEquations`. The resulting local order comparison applies to the actual self-pair of the supplied weak induction. The local supercuspidality criterion gives the unrestricted conclusion, and its totally complex specialization gives the second conclusion. `cyclicWeakInductionSupercuspidalFromPairEquations` gives the same conclusions from the completed global functional equations by restricting those equations to the required twists.

`CyclicWeakInductionSupercuspidalFromEqualSemilocalTCStatement` derives the totally complex
supercuspidality proposition from `EqualSemilocalEquationTCStatement` in the two universe
pairs. A number field extending a totally complex field is totally complex, so the
two equations supply the twist inputs over each of the given fields.
`cyclicWeakInductionSupercuspidalFromEqualSemilocalTC` applies the orbit identity and
two-twist comparison at those fields, then uses `cyclicWeakInductionSupercuspidalAt_of_gammaOrder`
on the supplied induction.

The derivation uses the two-twist comparison of Henniart and Herb, *Automorphic induction for GL(n) (over local non-archimedean fields)* (1995), Lemma 8.13 and §§8.14–8.17, and the local supercuspidality step of Proposition 5.5 used in Harris, *The local Langlands conjecture for GL(n) over a p-adic field, n < p* (1998), Proposition 4.8. The equal-rank functional-equation input uses Cogdell, *Analytic theory of L-functions for GL(n)* (2004), Theorem 2.2 and the proof of Theorem 4.1.

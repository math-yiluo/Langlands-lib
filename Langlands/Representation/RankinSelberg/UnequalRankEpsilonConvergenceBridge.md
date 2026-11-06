# Unequal-rank epsilon-to-gamma comparison from convergence

This is a derived interface for the reduction of Henniart's supercuspidal
local converse problem from epsilon factors to gamma factors. Its provenance
is the existing `AnalyticBridge`, `DualModels`, `EpsilonFactor`, and
`UnequalRankGammaFactor` APIs. It introduces no new source assertion and proves
no instance of the analytic or local converse theorems.

`UnequalRankConvergenceAt` means that each pair of functions in specified
coefficient models has an absolutely convergent unequal-rank integral on some
right half-plane. The half-plane may depend on the functions. It fixes the
larger rank independently of the two rectangular block indices, transporting
only their equality of natural-number dimensions.

Multiplicity one for the two Whittaker-functional spaces and nonzero chosen
functionals identify the intrinsic zeta values with rational continuations in
these models. The proof of `zetaValues_eq` specializes the published
`unequalRankZetaValues_eq_rationalValues`; the normalized-generator comparison
then rewrites by that equality. This comparison does not require separate
rationality, common-denominator, or generator-existence premises.

`IsUnequalRankEpsilonFactor.gammaFactor_of_convergence` retains all block
indices and every nonzero functional in the universal factor relation. Its
hypotheses are Whittaker type for the original and inverse-transpose pairs,
convergence of both model families, a compatible quotient Haar measure,
residue parameter `q > 1`, and certified intrinsic original and dual
L-polynomials. The proof first uses uniqueness of the compatible quotient
measure, then identifies the intrinsic polynomials with the generators in the
epsilon equation using convergence and multiplicity one. For the dual family
it applies the published inverse-transpose model comparison, exchanging the
rectangular block indices. The existing fixed-functional gamma comparison
concludes the universal gamma equation for the rational gamma expression on
its full regular domain.

Finally, `IsPairEpsilonFactor.gammaFactor_of_convergence_of_L_eq_one` specializes
both intrinsic L-polynomials to one. The rational gamma expression then
simplifies to the epsilon monomial. The original and dual convergence and
L-polynomial hypotheses remain explicit: this result alone does not prove
supercuspidal L-factor vanishing or Henniart's local converse theorem. The field
and two representation carriers have independent universes.

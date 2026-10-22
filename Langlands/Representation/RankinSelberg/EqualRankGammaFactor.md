# Equal-rank gamma with its universal JPSS relation

Worker 31. The constructor `Langlands.RankinSelberg.equalRankGammaFactor`
returns a unit rational function together with a proof of the existing
`IsPairGammaFactor` relation for a pair on `GL_(n+1)(F)`. Its underlying unit is
the published ratio

\[
G(X)=\epsilon(X)\frac{L^\vee(q^{-1}/X)}{L(X)}
    =cX^m\frac{P(X)}{P^\vee(q^{-1}/X)}.
\]

The construction requires epsilon existence and explicit original and dual
Whittaker-type and analytic hypotheses. It derives existence of both intrinsic
L-polynomials from those hypotheses, then proves that the resulting ratio
satisfies the universal relation. This is an equal-rank construction, including
rank one (`n = 0`); it does not discharge analytic existence or the unequal-rank
comparison.

## Original sources and derived scope

Jacquet--Piatetski-Shapiro--Shalika, *Rankin--Selberg Convolutions*, American
Journal of Mathematics 105 (1983), Section 2.1, formulas (3)--(4), printed p.386,
defines the coefficient functions and their inverse-transpose duals. Theorem
2.7(ii)--(iii), printed p.391, gives the reciprocal-polynomial normalization
`L = 1/P`, `P(0) = 1`, and the equal-rank normalized functional equation. The
ratio above is its algebraic rearrangement. The factor
`omega_sigma(-1)^(rank(pi)-1)` remains outside gamma. In Lean this is the
model scalar `zeta^n`. These original pages were visually read in the registered
source `jpss-1983-rankin-selberg`, SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.

Gerald B. Folland, *A Course in Abstract Harmonic Analysis*, second edition
(2015), Section 2.6, Proposition 2.50 and Theorem 2.51, printed pp.62--63,
formula (2.52), states the invariant quotient measure theorem and fixes the
normalizing scalar by the Weil integration formula. These pages were read in
`folland-2015-abstract-harmonic-analysis-second`, SHA256
`c82467bfa77428c32d3e1a5d1cbdc11129511e0c61da2f9d8fbc717776b9e542`.
The already published `UnipotentQuotient` module specializes this theorem to
the left quotient `N \ GL`, with fixed normalized ambient and subgroup Haar
measures. It uses the unimodular specialization and the opposite quotient
convention via inversion. This module imports its exact uniqueness theorem;
it does not assert uniqueness for arbitrary independently normalized measures.

The present construction is derived content: it composes the published
`PairFactors`, `GammaFactor`, `AnalyticBridge`, `DualModels`, and
`UnipotentQuotient` APIs. In particular, it does not reproduce the analytic
proof of JPSS Theorem 2.7. No new integral, Haar normalization, Fourier transform,
Whittaker model, or factor relation is introduced. The dual pair is the actual
inverse-transpose pullback with additive character `psi.scale (-1)`; identifying
it with a smooth contragredient remains a separate theorem obligation.

## Parameters and hypotheses

The field, first carrier and second carrier have independent universes `uF`,
`uV`, and `uW`. All representations are complex-linear; no finite dimensionality
of their carriers is imposed. Both representations act on `GL_(n+1)(F)` for an
arbitrary natural number `n`.

The universal comparison uses a nonarchimedean local field with its topology,
valuative relation and measurable structure. The group, upper unipotent
subgroup, and left unipotent quotient have Borel measurable structures. The
constructor also requires `BorelSpace F`, `T2Space F`, and
`TotallyDisconnectedSpace F` for the existing `IsSelfDual psi nu` input.
Right invariance of the fixed subgroup Haar measure is supplied by the
published instance, rather than a new assumption in this file.

`q : Nat` with `1 < q` and `abv : AbsoluteValue F Real` are explicit parameters.
The module does not identify arbitrary values of these parameters with the
residue cardinality and normalized absolute value. P-adic consumers supply
those particular parameters. The selected quotient measure `mu` satisfies the
full unchanged `IsCompatible` relation with `generalLinearHaar F n` and
`unipotentHaar F n`; the additive Haar measure `nu` is self-dual for `psi`.

Four Whittaker-type hypotheses concern the original pair for `psi` and its
inverse character, and the inverse-transpose pair for `psi.scale (-1)` and its
inverse. `IsOfWhittakerType` retains admissibility, finite generation over the
group algebra, and an exactly one-dimensional functional space. For every pair
of nonzero original functionals, `hA` supplies `EqualRankAnalyticConclusion` for
their coefficient models at `mu`; `hAd` supplies that conclusion for the
constructed first and second dual functionals at the same measure. These
conclusions include right-half-plane convergence, rational continuation, common
denominator and normalized-generator existence. They remain explicit inputs.
The epsilon input is `PairEpsilonFactorExists` for the same `q`, character,
absolute value, additive measure, and representations.

## Implemented proof and construction

`EqualRankEpsilonEquation.gammaEquation` is a fixed-functional lemma over the
more general field/topological-ring setting of the imported equations. It
accepts normalized generators `P` and `Pdual` for the original and transformed
rational-value families. An epsilon equation contains its own such generators;
uniqueness equates them with the supplied pair. A normalized generator supplies
a nonzero original rational value. For each model-vector pair and Schwartz test,
the lemma retains the epsilon equation's Fourier partner and continuations,
then applies `NormalizedFunctionalEquation.gamma_value_of_regular`.

The conclusion uses exactly the published `GammaFunctionalEquation` domain:
only zeros of the reduced denominators of `R` at `q^(-s)`, `Rdual` at
`q^(-(1-s))`, and `G` at `q^(-s)` are excluded. No extra exclusion for a zero of
the displayed `Pdual` remains; canceled zeros are covered by the imported
rational-identity argument.

`IsEqualRankEpsilonFactor.gammaFactor` supplies the universal relation for
`rationalGammaExpression`. It preserves the epsilon relation's witnesses of
compatible-measure and nonzero-functional existence. Given any compatible
quotient measure, two applications of `unipotentQuotientHaar_unique` identify
it with `mu`. For arbitrary nonzero functionals, the original analytic bridge
and `dualEqualRank_isLPolynomial_iff` turn the intrinsic L-polynomial predicates
into the required normalized-generator predicates. The preceding lemma then
applies to the epsilon equation for those same functionals and measure. The
dual comparison uses all Schwartz tests already present in its value family;
no Fourier-surjectivity assumption is added.

`pairGammaFactor_isPairGammaFactor_equalRank` applies that universal comparison
to the epsilon and intrinsic-polynomial witnesses selected by the published
constructors. `pairGammaFactor_eq_expression` identifies their ratio with the
expression above, and the equal-rank branch lemmas give `IsPairGammaFactor`.
This theorem also works with externally supplied original and dual polynomial
existence proofs; normalized-generator uniqueness ensures compatibility.

`equalRank_pairLPolynomialsExist` extracts nonzero functionals from the epsilon
relation, applies the original and dual analytic conclusions, and uses the
published intrinsic-generator existence theorem. The dual nonzero-functional
hypotheses are discharged by `firstDualFunctional_ne_zero` and
`secondDualFunctional_ne_zero`. Hence neither intrinsic L-polynomial existence
proof needs to be supplied separately to the final constructor.

`equalRankGammaFactor` applies this existence lemma, constructs the existing
unit `pairGammaFactor`, and pairs it with the universal relation just proved.
The property quantifies over every compatible quotient measure and all nonzero
functionals, with every coefficient-model vector pair and Schwartz test. The
existing `IsPairGammaFactor.unique` applies to the property and identifies any
two resulting rational functions when `q > 1`. The construction makes no claim
of unequal-rank compatibility, rank exchange, character-change or twist laws,
contragredient identification, nongeneric classification, or unconditional
analytic and epsilon existence.

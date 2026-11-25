# Closed convergence and vanishing comparison targets

Waldspurger (2003), III.6, printed pp.271–272, defines the Schwartz space
and its normalized constant terms. The estimates behind convergence are
in II.4.5, printed pp.262–263. VIII.2.1, printed pp.321–322, characterizes
the recursively projected cuspidal space by vanishing of all proper
semistandard induced constant terms. VIII.4, printed p.327, asserts
absolute convergence of the split-central integral on all Schwartz
functions. This module states the convergence obligations and the
standard vanishing comparison without assuming those analytic estimates.

## Closed targets

All three proposition definitions range over arbitrary nonarchimedean
local fields `F : Type u`, affine locally finite type connected reductive
group schemes `G`, a maximal split torus `i : S → G`, a generic
cocharacter `ν`, a compact open subgroup `K` with the displayed minimal
Iwasawa factorization, and a closed matrix representation `ρ` defining
the height. The topology of `G(F)` is the canonical rational-point
topology; its measurable space is Borel. These are structural inputs.
There is no characteristic-zero, split-group, quasi-split or positive-rank
restriction.

`RationalSchwartzCentralConvergenceStatement` further quantifies a split
component `s : T → G`, a Haar measure `muA` on its literal point-image
`A_G(F)`, and a continuous unitary character `χ` of that image. Its
conclusion is `CentralIntegralConvergesOn ⊤ muA χ`: for every actual
Schwartz function and every group argument, the integrand
`χ(a)⁻¹ f(a g)` is Bochner integrable. No `CentralWeights`, split-centre
height estimate or central convergence is a premise. The already proved
`centralIntegralOn` and exact range/span identities therefore give
linearity and exact-image comparisons on any submodule once this target
is established.

`RationalSchwartzConstantTermConvergenceStatement` asserts Bochner
integrability of `u ↦ f(x u y)` for every Schwartz function, every proper
standard finite root subset, every Haar measure on its actual radical,
and every `x,y ∈ G(F)`. Properness is inequality with the full simple-root
set, as in `rationalCuspidalSubmodule`. In rank zero this quantifier is
empty. There is no assumed `ConstantTermEstimate`. This target does not
duplicate the stronger Schwartz-valued constant-term estimate.

`RationalStandardConstantTermsVanish` is the separate vanishing-only
predicate for every such standard parabolic, measure and pair of
arguments, using `constantTermInd` and
`standardUnipotentModulus`. Its formula is
`δ(m)^(1/2) ∫ f(g₂⁻¹ m u g₁) du = 0`.
`RationalCuspidalVanishingComparisonStatement` asserts, for every actual
Schwartz function with the structural inputs above, equivalence of this
vanishing-only condition with membership in the constructed integrable
cuspidal kernel. It has no convergence premise.

## Proven implication and scope

`RationalSchwartzConstantTermConvergenceStatement.vanishingComparison`
proves the implication between the two closed propositions. It uses the
proved normalized membership characterization. The forward direction
forgets integrability; the reverse supplies integrability from the
constant-term convergence proposition and retains the given vanishing.
This elementary logical implication does not prove either analytic
target.

The first two targets are precise consequences of the source's
convergence assertions. The vanishing-only comparison and its implication
are internal formulations supporting the convergence-strengthened kernel.
They are distinct from comparison with the full semistandard index, and
from comparison with the recursive VIII.2 projection. Neither recursive
comparison direction is established here: that source projection
subtracts weighted proper-parabolic Fourier synthesis using strictly
smaller semisimple rank and VII.1.2/VII.2.5. No supplied projector,
same-rank finite support or Plancherel assertion appears in these targets.

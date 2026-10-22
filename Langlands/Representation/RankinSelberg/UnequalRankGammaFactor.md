# Unequal-rank gamma with its universal JPSS relation

Worker 31. `Langlands.RankinSelberg.unequalRankGammaFactor` constructs a unit
rational function together with a proof of the published `IsPairGammaFactor`
relation for ranks `r+1 > n+1`. It covers every rectangular block
`r = n + (j+k+1)`. The underlying unit is the existing ratio

\[
G(X)=\epsilon(X)\frac{L^\vee(q^{-1}/X)}{L(X)}
    =cX^m\frac{P(X)}{P^\vee(q^{-1}/X)}.
\]

The constructor derives common intrinsic original and dual L-polynomials from
the uniform epsilon equation and explicit analytic comparisons. It does not
infer a common polynomial merely from separate existence for each block.
Original and dual Whittaker type, per-block analytic conclusions, and epsilon
existence remain hypotheses. Equal ranks, reversed rank order, and analytic
existence are outside this module's construction.

## Original sources and derived scope

Jacquet--Piatetski-Shapiro--Shalika, *Rankin--Selberg Convolutions*, American
Journal of Mathematics 105 (1983), Section 2.1, formulas (3)--(4), printed p.386,
defines the actual coefficient models and inverse-transpose dual functions.
Theorem 2.7(ii)--(iii), printed p.391, specifies `L = 1/P` with `P(0) = 1`,
independence of the rectangular block, and the unequal-rank normalized epsilon
equation (2). Its complementary block is `k = rank(pi)-rank(sigma)-1-j`.
In this module's indexing that is exactly `r = n+(j+k+1)`.
The first transformed function is right-translated by the block Weyl element;
that translation is retained by the imported `DualModels` family equality.
The central-character factor stays outside gamma: it is `zeta^r`, corresponding
to the source exponent `rank(pi)-1`.

These passages were visually read in the registered original
`jpss-1983-rankin-selberg`, SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The algebraic rearrangement and transport of the already implemented families
are derived formal content; this module does not implement the source's
analytic existence proof.

Gerald B. Folland, *A Course in Abstract Harmonic Analysis*, second edition
(2015), Section 2.6, Proposition 2.50 and Theorem 2.51, printed pp.62--63,
formula (2.52), determines the invariant quotient measure when the ambient and
subgroup Haar measures are fixed. Those pages were read in
`folland-2015-abstract-harmonic-analysis-second`, SHA256
`c82467bfa77428c32d3e1a5d1cbdc11129511e0c61da2f9d8fbc717776b9e542`.
The proof uses the published `unipotentQuotientHaar_unique`, which specializes
that result to the actual normalized left quotient `N \ GL`. Its underlying
construction converts Folland's quotient convention by inversion and uses
proved unimodularity. This module adds no measure construction or normalization.

The imports are `PairFactors`, `GammaFactor`, `DualModels`, and
`UnipotentQuotient`. The original analytic comparison is inherited through
`DualModels`. All integrals, characters, coefficient images, polynomial
normalizations, rational reflection and gamma relation are reused.
The dual pair means inverse-transpose pullbacks for `psi.scale (-1)`; no
identification with the smooth contragredient is made here.

## Parameters and retained obligations

`F : Type uF` is a nonarchimedean local field with its field, valuative relation,
topology and measurable structure. The two complex-linear representation
carriers have independent universes `uV` and `uW`. The representations act on
`GL_(r+1)(F)` and `GL_(n+1)(F)`, with `n < r`. The smaller group, its upper
unipotent subgroup, and its left quotient have Borel measurable structures.
The universal measure comparison uses the quotient Borel structure. The final
constructor additionally has `BorelSpace F`, `T2Space F`, and
`TotallyDisconnectedSpace F` for the existing self-duality predicate. The
published unipotent Haar right-invariance instance is reused.

`q : Nat`, `1 < q`, and `abv : AbsoluteValue F Real` remain explicit parameters.
P-adic consumers use the residue cardinality and normalized absolute value;
no assertion identifies arbitrary parameters with those choices. The quotient
measure `mu` is compatible with the fixed normalized ambient and unipotent
Haar measures. The additive measure `nu` is self-dual for `psi`, and the block
measure is exactly `rectangularMeasure nu j (n+1)`.

Four hypotheses assert Whittaker type for the original first and second
representations with the standard and inverse-standard characters, and for
the inverse-transpose pair with the corresponding characters of
`psi.scale (-1)`. Each Whittaker-type predicate includes admissibility,
finite generation over the group algebra, and a one-dimensional functional
space; it does not impose finite-dimensional representation carriers.

For every pair of nonzero original functionals and every block `j,k`, `hA`
supplies the original analytic conclusion at `mu`, and `hAd` supplies the
analytic conclusion for their constructed first and second dual functionals
at `mu`. The dual conclusion is available for every block, so the proof can
use it at the complementary indices `k,j`. Each conclusion retains convergence
on right half-planes, rational continuation, common-denominator boundedness,
and normalized-generator existence. These facts and epsilon existence are
explicit inputs, not assertions obtained from choice.

All natural `n` are allowed, including a rank-one smaller representation when
`n = 0`. Both rectangular indices may be zero; the smallest rank gap has
`j = k = 0`. There is no reversed-rank branch in this construction.

## Fixed-rank analytic interface

`UnequalRankAnalyticAt j k hr` is the existing
`UnequalRankAnalyticConclusion j k` transported along the equality
`hr : r = n+(j+k+1)`. Its body substitutes this equality of natural numbers and
returns the old proposition. It adds no mathematical assumption or new
convergence claim. The field/topological-space setup of this wrapper is more
general than the local-field setup of the final constructor.

`UnequalRankAnalyticAt.isNormalizedGenerator_iff` similarly substitutes the
dimension equality and applies the published analytic bridge. It identifies
the normalized-generator predicate for `unequalRankZetaValuesAt` with the one
for `unequalRankValuesAt`, assuming Whittaker type and the two functional
nonvanishing hypotheses.

## Implemented proof and constructor

`UnequalRankEpsilonEquation.gammaEquation` takes normalized generators `P`
and `Pdual` for every original and transformed block family. Its epsilon
equation supplies another common pair. The original and dual families at
`j = 0`, `k = r-n-1` identify these polynomial pairs by uniqueness. For every
block, a normalized generator supplies a nonzero original rational value.
The proof retains the same continuations from the epsilon equation and applies
`NormalizedFunctionalEquation.gamma_value_of_regular` to obtain the gamma
equation. This uses the full common reduced-denominator domain of the original
continuation, reflected dual continuation and gamma; no extra exclusion of
canceled polynomial zeros is introduced.

`IsUnequalRankEpsilonFactor.gammaFactor` retains the epsilon relation's
compatible-measure and nonzero-functional existence witnesses. For every other
compatible measure, two applications of exact normalized quotient uniqueness
identify it with `mu`. For each nonzero functional pair and each block, the
fixed-rank analytic comparison matches the intrinsic original polynomial with
the model-family generator. `dualUnequalRankRationalValuesAt_eq` turns the
transformed dual family into the inverse-transpose model family at `k,j`, with
the prescribed block-Weyl translation already incorporated. The dual analytic
comparison then matches the intrinsic dual polynomial. The fixed-functional
lemma proves the universal unequal-rank relation.

`pairGammaFactor_isPairGammaFactor_unequalRank` applies this comparison to the
chosen witnesses of the existing pair epsilon and L-polynomial constructors.
It rewrites the unit ratio using `pairGammaFactor_eq_expression`, then uses the
unequal-rank branch of `IsPairGammaFactor`. Thus external intrinsic L-existence
proofs also yield the same universal specification under the stated hypotheses.

`unequalRank_pairLPolynomialsExist` derives the two intrinsic existence inputs
needed by the final constructor. It extracts nonzero functionals from epsilon
existence and applies their epsilon equation at `mu`. That equation supplies
one pair `P,Pdual` generating all original and transformed block families.
For each original block, the analytic comparison proves that this same `P`
generates the intrinsic values. To obtain the intrinsic dual generator at
`j,k`, the proof takes the transformed family of the original block `k,j` and
uses the dual-family equality and dual analytic comparison. Hence one
`Pdual` works for every intrinsic dual block. No independent choice is made
for different blocks.

`unequalRankGammaFactor` uses these derived existence proofs to construct
`pairGammaFactor` and pairs the unit with its proved `IsPairGammaFactor`
property. That property quantifies over all compatible quotient measures,
nonzero functional pairs, blocks and coefficient-model vectors. The existing
`IsPairGammaFactor.unique` identifies any two resulting rational functions
for `q > 1`. The module proves this conditional specification; it does not
prove the analytic or epsilon existence hypotheses, automatic dual Whittaker
type, contragredient identification, rank exchange, additive-character or twist
laws, or nongeneric Langlands classification.

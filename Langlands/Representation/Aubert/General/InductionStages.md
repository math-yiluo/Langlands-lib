# Normalized smooth induction in stages

Author: Worker 438.

This is an internal deduction from the published actual-subgroup normalized
induction, smooth induction in stages, smooth split-quotient comparison, and
character-twist equivalence. It constructs a natural isomorphism of the actual
functors; it introduces no new representation-theoretic premise or external
literature assertion. The rational specialization and the final Aubert identity
are separate obligations.

Let `G : Type uG` be a locally compact nonarchimedean group. Fix actual
subgroups with semidirect decompositions `h₀ : P₀ = M₀ ⋉ U₀`,
`h₁ : P₁ = M₁ ⋉ U₁`, and `hL` for the literal decomposition
`P₀.subgroupOf M₁ = (M₀.subgroupOf M₁) ⋉ (U₀.subgroupOf M₁)`.
Assume `P₀ ≤ P₁`, `M₀ ≤ M₁`, `U₁ ≤ U₀`, closedness of `M₁`, `U₀`,
and `U₁`, and continuity of the coarse projection `h₁.projection`.
The radicals `U₀`, `U₁`, and `U₀.subgroupOf M₁` satisfy the published
`Jacquet.Localization.IsLimitOfCompactSubgroups` condition.

`inductionStagesInnerModulus` is the positive conjugation Haar character of
`U₀.subgroupOf M₁`, restricted to `M₀.subgroupOf M₁` and transported to `M₀`.
The remaining normalization input `hδ` states that the positive character of
`U₁`, restricted from `M₁` to `M₀`, times this inner character equals the
positive character of `U₀` on `M₀`. The Haar convention is the one in the
imported constructors: `c • map(conjugation, μ) = μ`.

Under these hypotheses `normalizedInductionStagesIso` has source
`leviNormalizedInductionFunctor hM hMM hL hU₀ ⋙ normalizedInductionFunctor h₁ hU₁`
and target `normalizedInductionFunctor h₀ hU₀`. The input is the full smooth
representation category of `M₀` with coefficient carriers in `Type uV`; the
output carriers lie in `Type (max uG uV)`. Both carrier universes remain
independent. There is no finite-length or admissibility assumption.

The proof first compares the inducing coefficients. The private
`halfCharacter_stages` writes an element of `P₀.subgroupOf M₁` as its fine Levi
part times its inner radical part. The coarse positive character is trivial on
the inner radical by the published compact-subgroup-limit character lemma.
The unimodularity consequences for the radicals and `hδ` then give equality
of the half characters, using the multiplicative positive square-root map.
The actual restricted and ambient projections agree by
`IsSemidirectDecomposition.projection_subgroupOf`.

The direct inducing representation, read on `P₀.subgroupOf P₁`, is trivial on
the kernel of the coarse projection because `U₁ ≤ U₀`. On the coarse Levi
section, it equals the inner inducing representation twisted by the coarse
half character. The private `weightedSplitEquiv` absorbs that character into
smooth induced functions and applies the split-quotient equivalence. Inducing
this coefficient equivalence to `G` and applying `smoothStagesEquiv` yields
`normalizedInductionStagesEquiv`. The component construction
`normalizedInductionStagesAppIso` packages it in the literal functor objects.

`normalizedInductionStagesAppIso_eval` proves the concrete formula
`flatten(F)(x) = F(x)(1)`: the weighting character is evaluated at the identity
and hence contributes the scalar one. Naturality follows by this formula,
postcomposition for normalized induction, and extensionality of smooth
functions. `NatIso.ofComponents` supplies the natural isomorphism and both
inverse laws come from the component representation equivalences.

# Maps to unramified twists separate the vectors of `ind_{⁰G}^G ρ₀`

Module `Langlands.Representation.CuspidalSupport.RationalSummandTwistSeparation`, namespace
`Langlands.CuspidalSupport`.

This module is an internal helper. It supports the Lean proof `bernsteinInvariantCenterInclusion`
of Renard 2026, VI.10.4, `ℨ_D^{W(D)} ⊂ ℨ_Ω`
(`CuspidalSupport/BernsteinBlockCenterFunctionsInvariantCenterProof`). The argument is the
separation step of the published proof of Renard VI.4.3, Corollary (ii)
(`NormalHecke.commute_of_rank_le_one` in `NormalSubgroupHeckeCommutative`), stated for one
vector instead of an endomorphism.

## Statement

`rationalNormKernelSummandInduction_eq_zero_of_forall_twist`. Let `G` be an affine group
scheme, locally of finite type, over a non-archimedean local field `F`, with `G(F)` carrying
`rationalPointTopology`. Let `ρ₀` be a smooth representation of the common norm kernel
`⁰G = rationalCommonNormKernel G` (carriers in `Type uV`), `π` a smooth representation of
`G(F)` (carriers in `Type (max uF uV)`), and `j : ρ₀ → π|_{⁰G}` an injective `⁰G`-equivariant
linear map. Let `f ∈ Π = rationalNormKernelSummandInduction G ρ₀ = ind_{⁰G}^{G(F)} ρ₀`. If
`U f = 0` for every unramified character `ω` (`unramifiedCharacters` of the rational norm
characters) and every map `U : Π → π ⊗ ω` (`rationalUnramifiedTwist G ω π`), then `f = 0`.

No irreducibility is assumed.

## Proof

Write `H = ⁰G`, open (`isOpen_rationalCommonNormKernel`) and normal, so `G(F)/H` is discrete
(`QuotientGroup.discreteTopology`). Let `t(Hx) = π(x⁻¹) j(f(x))`, the coset terms
`Induction.cosetTerm` of `f` for `j`; `t` has finite support (`hasFiniteSupport_cosetTerm`).

First `t = 0`, by `NormalHecke.eq_zero_of_forall_character` (Dedekind's independence of
characters with vector coefficients) on the group `G(F)/H`, with the injection
`NormalHecke.leftQuotientEquiv : H\G(F) ≃ G(F)/H` and the separation of
points of `G(F)/H` by characters (`rationalNormKernelQuotient_exists_character_ne_one`). Let
`ω₀ : G(F)/H → ℂˣ` be a character. Since `G(F)/H` is discrete, `ω₀⁻¹` is continuous, and its
pullback `ω` (`quotientCharacterPullback`) is an unramified character. Let
`U : Π → π ⊗ ω` correspond, by Frobenius reciprocity for compact induction from the open
subgroup `H` (`NormalHecke.inducedHomEquiv`), to `j` viewed as a map into `(π ⊗ ω)|_H`
(`NormalHecke.twistRestrictEquiv`, as `ω` is trivial on `H`). The inverse reciprocity map is
the finite sum of coset terms (`Induction.cosetSum`), so
`0 = U f = ∑_{Hx} (π ⊗ ω)(x⁻¹) j(f(x)) = ∑_{Hx} ω₀(xH) t(Hx)`,
because `ω(x⁻¹) = ω₀⁻¹(x⁻¹H) = ω₀(xH)`. This is the hypothesis of Dedekind's lemma.

Then, for every `x`, `π(x⁻¹) j(f(x)) = 0`, so `j(f(x)) = 0`, so `f(x) = 0` by injectivity of
`j`, and `f = 0` (`Induction.compactFunctions_ext`).

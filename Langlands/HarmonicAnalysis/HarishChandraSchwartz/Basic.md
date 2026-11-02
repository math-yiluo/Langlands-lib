# Harish-Chandra Schwartz spaces for arbitrary weights

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.Basic`,
namespace `Langlands.HarishChandraSchwartz`.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, section III.6 (printed
p. 271, PDF p. 37). Waldspurger defines, for a locally constant function `f` on `G`
and `r ∈ ℝ`,

`ν_r(f) = sup { |f(g)| Ξ(g)⁻¹ (1 + σ(g))^r : g ∈ G }`,

where `Ξ` is the spherical function of II.1 and `σ = log ‖·‖` is the height of I.1.
For each compact open subgroup `H` of `G`, `C_H` is the space of functions in
`C(H \ G / H)` with `ν_r(f)` finite for every `r ∈ ℝ`, topologized by the norms `ν_r`.
Then `C(G) = ⋃_H C_H`, with `H` running over the compact open subgroups, and `C(G)`
carries the inductive-limit topology of the topologies of the `C_H`, cited as
[Bourbaki, *Espaces vectoriels topologiques*, ch. II, §4.6]. Property (1) of III.6
says: a linear map from `C(G)` to a locally convex complex topological vector space
is continuous if and only if its restriction to every `C_H` is continuous.

## Scope: generic weights

This module formalizes the construction only. The group `G` is an arbitrary
topological group and the weights `Ξ σ : G → ℝ` are arbitrary real functions. No
property of Waldspurger's `Ξ` and `σ` is used or assumed in the definitions, and
the module makes no claim about the actual weights. Results that need properties
of the weights take them as explicit hypotheses: positivity of `Ξ` and
nonnegativity of `σ` (both true for the source weights by II.1 and I.1). The
source weights are realized in separate modules.

## Definitions

- `IsBiInvariant H f`: `f (h₁ * g * h₂) = f g` for all `h₁ h₂ ∈ H` and all `g`.
  This is membership of `f : G → ℂ` in Waldspurger's `C(H \ G / H)`.
- `weight Ξ σ r g = ENNReal.ofReal (Ξ(g)⁻¹ (1 + σ(g))^r)`. Here `x^r` is the real
  power `Real.rpow`. For positive `Ξ` and nonnegative `σ` the argument is positive,
  so this is the real weight itself.
- `nu Ξ σ r f = ⨆ g, ‖f g‖ₑ * weight Ξ σ r g`, Waldspurger's `ν_r(f)`, valued in
  `ℝ≥0∞`. An infinite supremum is the value `∞`, so "`ν_r(f)` is finite" is
  `nu Ξ σ r f < ⊤`.
- `levelSubmodule Ξ σ H`: the complex subspace of `G → ℂ` of `H`-bi-invariant
  functions with `nu Ξ σ r f < ⊤` for every real `r`. For compact open `H` this is
  Waldspurger's `C_H`.
- `CompactOpenSubgroup G`: open subgroups of `G` whose underlying set is compact.
  `CompactOpenSubgroup.inf` is the intersection of two of them.
- `schwartzSubmodule Ξ σ = ⨆ K : CompactOpenSubgroup G, levelSubmodule Ξ σ K`.
  When `G` has a compact open subgroup and `G` is a topological group, membership
  is exactly membership in some level (`mem_schwartzSubmodule_iff`), so this is
  Waldspurger's union `C(G) = ⋃_H C_H`. The levels are directed because
  `levelSubmodule` is antitone in the subgroup and compact open subgroups are
  closed under intersection.
- `Level Ξ σ K`: the level `C_K` as a type. Its topology is defined by the
  seminorm family `r ↦ (nu Ξ σ r ·).toReal` over `r ∈ ℝ` (`Level.seminorm`,
  `Level.seminormFamily`, `Level.withSeminorms`). It is a topological additive
  group with continuous complex scalar multiplication and is locally convex.
- `Space Ξ σ`: the Harish-Chandra Schwartz space `C(G)` as a type, with
  `Space.ofLevel K : Level Ξ σ K →ₗ[ℂ] Space Ξ σ` the inclusions.
- `Space.originalTop`: the final topology of the inclusions, i.e. the finest
  topology making every inclusion continuous. It need not be a vector-space
  topology.
- `Space.topologicalSpace`: the topology of `C(G)`. It is the `sInf`, in Mathlib's
  order on topologies (where `≤` means finer), of all topologies `t` that are
  coarser than `originalTop` and make `C(G)` a topological additive group with
  continuous complex scalar multiplication that is locally convex over `ℝ`. This
  set is closed under infima, so the result is the finest locally convex vector
  space topology for which every inclusion `C_H → C(G)` is continuous. That is
  the locally convex inductive-limit topology cited by Waldspurger. The
  construction is the same one Mathlib uses for the LF topology on test functions
  (`Mathlib/Analysis/Distribution/TestFunction.lean`).
- `Space.ofLevelCLM K`: the inclusion `C_K → C(G)` as a continuous linear map.
- `Space.mkCLM T hT`: a continuous linear map on `C(G)` built from a linear map
  `T` and the continuity of every restriction `T ∘ ofLevel K`.
- `Space.toFunLinear`: the underlying-function map `C(G) → (G → ℂ)`.

## Proved properties

- `nu` is a seminorm-type functional: `nu_zero`, `nu_add_le`, `nu_smul`, `nu_neg`.
- For nonnegative `σ`, `weight` and `nu` increase with `r` (`weight_mono`,
  `nu_mono`).
- `norm_le_of_nu`: for positive `Ξ` and nonnegative `σ` and finite `ν_r(f)`,
  `‖f g‖ ≤ ν_r(f) Ξ(g) (1 + σ(g))^(-r)`.
- `Space.topologicalSpace_le_iff`: a locally convex vector space topology on
  `C(G)` is coarser than the topology of `C(G)` if and only if it is coarser than
  `originalTop`.
- `Space.continuous_ofLevel`: every inclusion `C_K → C(G)` is continuous.
- `Space.continuous_iff_continuous_comp`: Waldspurger III.6(1). For a complex
  topological vector space `V` that is locally convex over `ℝ` (with compatible
  real and complex scalar actions), a complex-linear `T : C(G) → V` is continuous
  if and only if `T ∘ ofLevel K` is continuous for every compact open subgroup `K`.
- `Space.continuous_eval_level` and `Space.continuous_toFunLinear`: for positive
  `Ξ` and nonnegative `σ`, point evaluations are continuous on every level, and the
  underlying-function map `C(G) → (G → ℂ)` is continuous for the product topology.
- `Space.t2Space`: for positive `Ξ` and nonnegative `σ`, `C(G)` is Hausdorff.

## Not covered here

The following parts of III.6 are left to later modules: the completeness of `C(G)`,
the inclusion and density of `C_c^∞(G)`, continuity of the `G × G` translation
action, Lemma III.6.1 on convolution, and the constant term `f ↦ f^(P)`. All of
these depend on properties of the actual weights `Ξ` and `σ`, which this module
does not assume.

# Normalized induction and localization for closed semidirect triples

This module constructs the functors `I_{U,θ}`, `i_{U,θ}` and `r_{U,θ}` of
Bernstein–Zelevinsky, *Induced representations of reductive p-adic groups I*
(1977), Section 1.8, for actual closed subgroups `M`, `U`, `P` of `G` with
`M` normalizing `U`, `M ∩ U = {1}` and `P = MU`, and a character `θ` of `U`
fixed by `M`. All declarations are in the namespace `Langlands.ClosedSemidirect`
of the module `Langlands.Representation.Induction.ClosedSemidirect`.
Author: Worker 149. The decomposition, inflation, covariance and raw induced
function layer extends the shared draft revision 1 of this task, which was
carried over from the previous instance.

Throughout, `G : Type uG` is a group with a topology. Representation carriers
`V : Type uV` and `W : Type uW` are complex modules with independent universes.
No topology on carriers, finite-dimensionality, irreducibility, admissibility or
finite length is assumed anywhere.

## The triple and its unique decomposition

`Triple G` records three actual subgroups `M`, `U`, `P : Subgroup G` and exactly
the source hypotheses:

- `closed_M`, `closed_U`, `closed_P`: each carrier is closed in `G`;
- `normalizes : M ≤ Subgroup.normalizer (U : Set G)`;
- `intersection : M ⊓ U = ⊥`;
- `product_eq : (P : Set G) = (M : Set G) * (U : Set G)`, the carrier of `P` is
  the pointwise product `MU`.

`product_eq_reverse` derives `P = UM` from the normalizer hypothesis, and
`M_le_P`, `U_le_P` the two inclusions. `conjugate m u` is the published
`Jacquet.Localization.conjugate`, with value `m * u * m⁻¹` (`conjugate_val`).

`combine u m : P` is the actual product `u * m` (`combine_val`).
`combine_bijective` proves that `(u, m) ↦ u * m` is a bijection `U × M → P`:
injectivity from `M ∩ U = {1}`, surjectivity from `P = UM`.
`decomposition : P ≃ U × M` is its inverse, the unique algebraic decomposition
`p = u * m`. `decomposition_combine`, `combine_decomposition`,
`decomposition_val` and `decomposition_unique` state that it inverts `combine`
and is the only such factorization. `combine_mul` and `decomposition_mul` give
the multiplication law

`(u * m) * (v * n) = (u * (m v m⁻¹)) * (m * n)`.

No continuity of the decomposition is asserted or assumed anywhere in this
module.

`projection : P →* M` sends `u * m` to `m`; its multiplicativity is the second
component of the multiplication law. `sectionM` and `sectionU` are the actual
inclusions of `M` and `U` into `P`. `projection_combine`, `projection_sectionM`
and `projection_sectionU` give its values, and `projection_eq_one_iff` proves
that its kernel is exactly `U`.

## The character and its inflation

`Character T` records `theta : T.U →* ℂˣ`, the field `locallyConstant`,
asserting that `u ↦ (theta u : ℂ)` is locally constant, and the field `invariant`,
the published proposition `Jacquet.Localization.IsInvariant`, which means
literally `θ(m u m⁻¹) = θ(u)` for all `m ∈ M`, `u ∈ U` (`theta_conjugate`).

`inflation : P →* ℂˣ` evaluates `θ` on the `U` component of the decomposition.
Multiplicativity follows from `decomposition_mul` and invariance of `θ`.
`inflation_combine`, `inflation_sectionM` and `inflation_sectionU` give
`θ(u)`, `1` and `θ(u)` on `u * m`, `m` and `u`.

## Covariance representation and raw induced functions

The following layer takes an arbitrary scalar character `ν : M →* ℂˣ`. It is an
internal assembly parameter, not asserted to be the modulus. The normalized
functors below use `ν = mod_U^{1/2}`. Downstream statements may use this layer
directly with that `ν`.

- `covarianceCharacter ν = inflation * (ν ∘ projection)`, with value
  `θ(u) ν(m)` at `u * m` (`covarianceCharacter_combine`).
- `covariance ν ρ : Representation ℂ P V` is the published scalar twist
  `Langlands.twist` of `ρ ∘ projection` by that character. `covariance_apply`
  gives its value at any `p`, and `covariance_combine` the value
  `(θ(u) ν(m)) • ρ(m) v` at `u * m`. No smoothness is assumed of `ρ`.
- `covarianceMap ν f` is an `M`-intertwiner `f` regarded as a `P`-intertwiner,
  with the same underlying linear map (`covarianceMap_apply`).
  `covarianceFunctor ν : Rep ℂ M ⥤ Rep ℂ P` bundles these; both functor laws
  hold by reflexivity. It keeps the carrier universe `uV`.

Assuming `[IsTopologicalGroup G]`, with the published constructors of
`Langlands.Representation.Induction.Definitions`:

- `SmoothFunctions ν ρ` and `CompactFunctions ν ρ` are
  `Induction.SmoothFunctions P (covariance ν ρ)` and
  `Induction.CompactFunctions P (covariance ν ρ)`, of universe `max uG uV`.
- `smoothAction ν ρ` and `compactAction ν ρ` are
  `Induction.smoothInduced` and `Induction.compactInduced`: right translation.
  `eval ν ρ f g` is the value of the underlying function.
- `eval_covariance` states BZ77 1.8(a)(1) for this `ν`:
  `f(u * m * g) = (θ(u) ν(m)) • ρ(m)(f(g))`.
  `eval_smoothAction` and `eval_compactAction` give
  `(g · f)(x) = f(x * g)`.
- `compact_support` states that an element of `CompactFunctions` has compact
  nonzero support in `P\G`, namely `Induction.quotientSupport`, the image of
  `Function.support f` in the left quotient.
- `smoothFunctionOf` builds an element of `SmoothFunctions` from a function
  `f : G → V` with exactly the covariance `f(u * m * g) = (θ(u) ν(m)) • ρ(m)(f(g))`
  and one open subgroup `K` with `f(g * k) = f(g)`. The covariance over all
  `p ∈ P` is derived from the decomposition. `eval_smoothFunctionOf` gives back
  `f`. `compactFunctionOf` adds exactly compactness of `Induction.quotientSupport P f`.
- `smoothMap ν f` and `compactMap ν f` are the published
  `Induction.smoothInducedMap` and `Induction.compactInducedMap` of
  `covarianceMap ν f`: postcomposition by `f` (`eval_smoothMap`,
  `eval_compactMap`).

## The modulus of conjugation on `U`

Assume `[LocallyCompactSpace G] [IsTopologicalGroup G]`.

- `Triple.modulus : M →* ℝ≥0ˣ` is the published
  `HaarModulus.closedRestrictCharacter U closed_U M normalizes`: the positive
  Haar modulus of `u ↦ m u m⁻¹` on the closed subgroup `U`.
- `halfModulus` and `inverseHalfModulus : M →* ℂˣ` are the published
  `HaarModulus.closedHalfCharacter` and `HaarModulus.closedInverseHalfCharacter`.
  `halfModulus_apply` and `inverseHalfModulus_apply` give the values
  `√(mod_U(m))` and `(√(mod_U(m)))⁻¹` as complex numbers, with the positive real
  square root. `inverseHalfModulus_eq_inv` states
  `inverseHalfModulus = halfModulus⁻¹`, and `halfModulus_sq` states that the
  square of `halfModulus m` is `mod_U(m)` in `ℂˣ`.
- `integral_conjugate_inv` records the BZ77 1.7 orientation: for a regular Haar
  measure `μ` on the Borel space `U`, and `f : U → E` with `E` a real normed space,
  `∫ f(m⁻¹ u m) dμ(u) = mod_U(m) • ∫ f dμ`.
  This is the source formula `∫ f(σ⁻¹(u)) dμ = mod_U(σ) ∫ f dμ` for
  `σ(u) = m u m⁻¹`. It follows from the published
  `HaarModulus.integral_normalizerConj_symm`.
- With `[NonarchimedeanGroup G]` instead of `[IsTopologicalGroup G]`,
  `isOpen_ker_halfModulus` and `isOpen_ker_inverseHalfModulus` give open kernels,
  from the published `HaarModulus.isOpen_ker_closed...` lemmas.

## Normalized induction `I_{U,θ}` and compact induction `i_{U,θ}`

Assume `[LocallyCompactSpace G] [IsTopologicalGroup G]`.
`inducingRepresentation ρ = covariance halfModulus ρ` is the representation
`u * m ↦ θ(u) mod_U^{1/2}(m) ρ(m)` of `P` (`inducingRepresentation_combine`).

```lean
normalizedInductionFunctor :
    SmoothRep.{0, uG, uV} ℂ T.M ⥤ SmoothRep.{0, uG, max uG uV} ℂ G
normalizedCompactInductionFunctor :
    SmoothRep.{0, uG, uV} ℂ T.M ⥤ SmoothRep.{0, uG, max uG uV} ℂ G
```

are the composites
`SmoothRep.toRep ⋙ covarianceFunctor halfModulus ⋙ Induction.smoothInductionFunctor P`
and the same with `Induction.compactInductionFunctor P`. Their functor laws and
the smoothness of every output are those of the published functors. Smoothness of
the input is not used by the construction. Induction raises the carrier universe
to `max uG uV`.

The exposed formulas are:

- `normalizedInductionFunctor_obj_representation` and
  `normalizedCompactInductionFunctor_obj_representation`: the actions are
  `smoothAction halfModulus` and `compactAction halfModulus`.
- `normalizedInductionFunctor_covariant`: BZ77 1.8(a)(1),
  `f(u * m * g) = θ(u) mod_U^{1/2}(m) • ρ(m)(f(g))`.
  `normalizedInductionFunctor_covariant_P` gives the same covariance for any
  `p ∈ P`, through `inflation` and `projection`.
- `normalizedInductionFunctor_exists_openSubgroup`: BZ77 1.8(a)(2), one open
  subgroup `K` with `f(g * k) = f(g)` for all `g` and `k ∈ K`.
- `normalizedInductionFunctor_obj_apply` and
  `normalizedCompactInductionFunctor_obj_apply`: the action is right translation,
  `(g · f)(x) = f(x * g)`.
- `normalizedInductionFunctor_map_eval`, `normalizedInductionFunctor_hom_map` and
  their compact counterparts: a morphism `φ` acts by postcomposition, and its
  underlying intertwiner is `smoothMap halfModulus φ` or
  `compactMap halfModulus φ`.
- `normalizedFunctionOf` constructs an element of `I_{U,θ}(ρ)` from exactly
  conditions (1) and (2) (`eval_normalizedFunctionOf`), and
  `normalizedCompactFunctionOf` an element of `i_{U,θ}(ρ)` from (1), (2) and
  compactness of its nonzero support modulo `P`.
- `compactToInduced` regards an element of `i_{U,θ}(ρ)` as an element of
  `I_{U,θ}(ρ)`. `normalizedCompactInductionFunctor_isCompact` records compact
  support modulo `P`. `compactInclusion A` is the inclusion as a morphism of
  smooth representations, from the published `Induction.compactInclusion`
  (`compactInclusion_apply`).

## Normalized localization `r_{U,θ}`

Assume `[LocallyCompactSpace G] [IsTopologicalGroup G]` for the action formulas.

- `localizedAction π` is the published twist `Langlands.twist inverseHalfModulus`
  of the published action `Jacquet.Localization.action π U θ M normalizes invariant`
  on `Jacquet.Localization.Coinvariants π U θ`. That carrier is the quotient of `V`
  by `Jacquet.Localization.relations π U θ`, the span of all
  `π(u) ξ - θ(u) ξ`, namely BZ77's `E(U,θ)`.
- `localizedAction_mk`: `m · [ξ] = mod_U^{-1/2}(m) • [π(m) ξ]`, the BZ77 1.8(b)
  formula.
- `localization_mk_apply`: `[π(u) ξ] = θ(u) • [ξ]`. `localization_ker_mk`: the
  kernel of the quotient map is exactly that span. These two hold without
  topology hypotheses.
- `localizedMap f` is the published `Jacquet.Localization.map` for a
  `G`-intertwiner `f`, viewed between the twisted actions by
  `Langlands.twistIntertwining`. `localizedMap_mk`: `[ξ] ↦ [f ξ]`.

With `[LocallyCompactSpace G] [NonarchimedeanGroup G]`,

```lean
normalizedLocalizationFunctor : SmoothRep.{0, uG, uV} ℂ G ⥤ SmoothRep.{0, uG, uV} ℂ T.M
```

is `Jacquet.Localization.smoothFunctor U θ M normalizes invariant ⋙
SmoothRep.twistFunctor inverseHalfModulus isOpen_ker_inverseHalfModulus`. The
functor laws and output smoothness are those of the published functors. The
openness of the twist kernel is proved, not assumed. Localization keeps the
carrier universe `uV`. `normalizedLocalizationFunctor_obj_representation`,
`normalizedLocalizationFunctor_obj_carrier`,
`normalizedLocalizationFunctor_obj_apply`, `normalizedLocalizationFunctor_map_mk`
and `normalizedLocalizationFunctor_hom_map` state by reflexivity that the action
is `localizedAction`, the carrier is the actual quotient `E / E(U,θ)`,
`m · [ξ] = mod_U^{-1/2}(m) • [π(m) ξ]`, a morphism acts by `[ξ] ↦ [f ξ]`, and
its underlying intertwiner is `localizedMap`.

## Hypotheses and scope

The source setting is an l-group: by BZ77 1.1 a Hausdorff topological group in
which every neighborhood of the identity contains an open compact subgroup. Such
a group is locally compact and nonarchimedean, so it satisfies every instance
used here. The constructions use less:

- The decomposition, projection, inflation and covariance layers use no topology.
  The raw induced-function layer uses `[IsTopologicalGroup G]`.
- The modulus, the normalized induction functors and the localized action use
  `[LocallyCompactSpace G] [IsTopologicalGroup G]`. `closed_U` makes `U` locally
  compact, so the published Haar modulus applies.
- The localization functor uses `[LocallyCompactSpace G] [NonarchimedeanGroup G]`,
  for the open kernel of `mod_U^{-1/2}`.
- No Hausdorff hypothesis is used, so it is not included in the Lean types.
  `closed_M`, `closed_P` and `locallyConstant` are recorded source hypotheses
  that the constructions do not use.
- Openness of `P`, compactness of `G/P`, admissibility, finite length and the
  condition that `U` is a limit of compact subgroups are not assumed.

Coefficients are `ℂ` with coefficient universe `0`, as in the source. This
module makes no assertion of exactness, adjunction, transitivity, the geometric
lemma or orbit-piece intersections, and none of them is an input field.

## Source and provenance

The original source is I. N. Bernstein and A. V. Zelevinsky, *Induced
representations of reductive p-adic groups I*, Ann. Sci. École Norm. Sup. (4) 10
(1977).

- Literature ID: `bernstein-zelevinsky-1977-induced-i`.
- Source SHA256: `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
- Retained original:
  `/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`.

Section 1.1, printed page 442 / PDF page 3, defines l-groups. Section 1.5, printed
page 443 / PDF page 4, defines characters as locally constant homomorphisms to
`ℂ^×`. Section 1.7, printed pages 443–444 / PDF pages 4–5, defines `mod_U` by
`∫ f(σ⁻¹(u)) dμ = mod_U(σ) ∫ f dμ` and `mod_U(g)` for `g` normalizing a closed `U`.
Section 1.8, printed pages 444–445 / PDF pages 5–6, states the setting
(closed `M`, `U`, `M` normalizes `U`, `M ∩ U = {e}`, `P = MU` closed, `θ`
normalized by `M`) and defines

- (a)(1) `f(umg) = θ(u) mod_U^{1/2}(m) ρ(m)(f(g))`;
- (a)(2) an open subgroup `K_f` with `f(gk) = f(g)`;
- the action `(δ(g) f)(g') = f(g' g)` of `I_{U,θ}(ρ)`, and `i_{U,θ}(ρ)` as the
  subspace of functions compactly supported modulo `P`;
- (b) `E(U,θ)`, the span of `π(u) ξ - θ(u) ξ`, the quotient `E / E(U,θ)`, and
  `δ(m)(ξ + E(U,θ)) = mod_U^{-1/2}(m) (π(m) ξ + E(U,θ))`.

Sections 5.1–5.3, printed pages 459–461 / PDF pages 20–22, use these functors in
the geometric lemma. All of these pages were read directly from the retained PDF.

The functors and their exposed formulas are source definitions. The following
are derived implementation, not separately numbered source results: the
decomposition and its laws, the projection, inflation and covariance
representation; the scalar parameter `ν`; the encoding of subgroups, closedness and
`P = MU` as fields; the reduction of the source definitions to the published
induction, localization and twist functors; and the weakened topological
hypotheses above.

## Implementation dependencies

Published Library modules: `Langlands.Group.HaarModulus` (modulus and half
characters), `Langlands.Representation.Induction.Definitions` (covariant
functions, smooth and compact induction), `Langlands.Representation.Jacquet.Localization`
(θ-coinvariants and their functor), `Langlands.Representation.Category.Twist`
(the smooth twist functor), and through them `Langlands.twist`,
`Langlands.twistIntertwining` and the bundled `SmoothRep` category. Mathlib supplies
`Subgroup.mul_injective_of_disjoint`, `Subgroup.set_mul_normalizer_comm` and the
`Rep` interfaces. All construction obligations are proved in this module or by
those published modules. The approved environment is
`bb168ec3-1031-46d9-816b-5c2ed7bbe1a6`, Lean 4.34.0, Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.

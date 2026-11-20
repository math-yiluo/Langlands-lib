# Restricting a Hecke character along an extension of degree one

Module `Langlands.Automorphic.RankOneHeckeRestriction`, namespace
`Langlands.Automorphic.RankOneHecke`. Author: Worker 5086 (Task 7783). These are internal
helper results and cite no source. The module sets `autoImplicit false`.

Throughout, `K ⊆ L` are number fields in one universe `u` (`Algebra K L`), and
`h : Module.finrank K L = 1`. Only the results marked "without `h`" drop this hypothesis.

- `restriction ξ := ξ.comp ideleClassInclusion` is a Hecke character of `K` for every Hecke
  character `ξ` of `L`. Here `ideleClassInclusion : C_K → C_L` is the published idele-class
  inclusion. This definition needs no `h`.

## Places in degree one

- `ramificationIdx_mul_inertiaDeg_eq_one`, `ramificationIdx_eq_one` and `inertiaDeg_eq_one`:
  every finite place `q` above a finite place `p` has `e(q|p) = f(q|p) = 1`. The published
  `finitePlacesAbove_sum_ramification_inertia` gives `∑ e f = [L : K] = 1`, and every term is
  at least `1` (Mathlib's `ramificationIdx_pos` and `inertiaDeg_pos`).
- `card_finitePlacesAbove` and `finitePlacesAbove_eq`: exactly one finite place lies above each
  finite place.
- `card_infinitePlacesAbove` and `infinitePlacesAbove_eq`: exactly one place lies above each
  complex place. The published `infiniteLocalDegree_sum` gives
  `∑ [L_w : K_v] = [L : K] = 1`, and every local degree is `1` above a complex place
  (`isUnramified_of_isComplex`, module `ComplexPlaceParameterNorm`, candidate `78761ac6`).

## Finite components

- `restriction_finiteComponent`: `(restriction ξ)_p(a) = ξ_q(ι_q a)` for the place `q` above
  `p`, where `ι_q` is the published completion map `FiniteExtension.completionMap p q`. The
  published `ideleInclusion_ofAdicCompletion` writes the inclusion of a single-place idele as a
  product over the places above `p`, and that product has the single factor at `q`.
- `restriction_finiteUniformizerValue`: if `ξ` is unramified at `q`, then
  `(restriction ξ).finiteUniformizerValue p = ξ.finiteUniformizerValue q`. The chosen
  uniformizer of `K_p` has valuation `exp(-1)`, and so does its image, because
  `v_q(ι_q x) = v_p(x)^e` with `e = 1` (published `valuation_completionMap`). The published
  `finiteComponent_eq_finiteUniformizerValue` evaluates an unramified character at any element
  of valuation `exp(-1)`.
- `presentation_restriction_isWeakInductionOf`: the spectral system of
  `presentation (restriction ξ)` is weakly induced from `ξ` in the sense of the published
  `SpectralSystem.IsWeakInductionOf`. The rank is `0 + 1 = [L : K]`. Let `T` be a finite set
  outside of which `ξ` is unramified (published `exists_finset_isUnramifiedAt`). At the
  cofinitely many `p` with no place of `T` above them (published `eventually_avoidsAbove`),
  every place above `p` has `e = 1` and `ξ` is unramified there. For every uniformizer family
  `ϖ`, the induced Euler polynomial `∏_q (1 - ξ_q(ϖ_q) X^(f(q|p)))` has the single factor
  `1 - ξ.finiteUniformizerValue q · X`, which is the Euler polynomial
  `1 - (restriction ξ).finiteUniformizerValue p · X` of the presentation.
- `cuspidal_restriction_isWeakAutomorphicInductionOf`: `(cuspidal (restriction ξ)).isoClass`
  is a weak automorphic induction of `ξ`, at universes `.{u, u, uP}`.

## Infinite components

- `ideleInclusion_infiniteIdeleInclusion`: for a complex place `v` with the place `w` above it,
  the idele inclusion sends the idele equal to `x` at `v` (and `1` elsewhere) to the idele
  equal to `LiesOver.completionMap x` at `w` (and `1` elsewhere). At `w` this is the published
  `infiniteCompletionMap_comap_eq`. Any other place lies over a place other than `v`, by
  uniqueness above `v`. The finite part is `1`.
- `restriction_infiniteComponent`: `(restriction ξ)_v(x) = ξ_w(LiesOver.completionMap x)`.
- `restriction_hasComplexPlaceParameter`: if `ξ` has the parameter `d` at the place `w` above the
  complex place `v`, then `restriction ξ` has the parameter `normParameter v w d` at `v`. This
  is `d` when the embedding of `w` restricts to that of `v`, and `d̄` otherwise. It uses the
  coordinate formulas `extensionEmbedding_completionMap_of_comp_eq` and `_of_comp_ne` (module
  `ComplexPlaceParameterNorm`).
- `complexPlaceLanglandsSum_fin_one` holds without `h`. For an enumeration `e : Fin 1 ≃` of
  the places above `v`, the published `complexPlaceLanglandsSum v e (fun w => [a w])` is
  `[normParameter v (e 0) (a (e 0))]`.

## Complex conjugation

These results hold without `h`, for CM fields `K` and `L`.

- `complexConj_algebraMap`: `c_L (a) = c_K (a)` for `a ∈ K`, where `c_K`, `c_L` are Mathlib's
  `IsCMField.complexConj`. Every complex embedding `φ` of `L` turns `c_L` into complex
  conjugation, `φ ∘ algebraMap` is an embedding of `K`, and `φ` is injective.
- `restriction_ideleClassComplexConj`: if `ξ ∘ c = ξ⁻¹` on idele classes, then the same holds
  for `restriction ξ`. The idele-class inclusion intertwines the conjugations, by the published
  `ClassField.Global.ideleClassInclusion_ideleClassEquiv`.

## Algebraic characters

These results hold without `h`.

- `exponentData_conj`: `(exponentData a b).conj = exponentData b a`.
- `hasComplexPlaceParameter_of_atInfinity` assumes `L` totally complex and that the
  archimedean character `ξ.atInfinity` is the published `InfinityType.toCharacter t` of an
  infinity type `t`. Then at every complex place `w` the character `ξ` has the parameter
  `exponentData (t σ) (t σ̄)`, where `σ = w.embedding`. In the product defining `toCharacter t`
  at the idele supported at `w`, the only factor that is not `1` is the one at `w`.

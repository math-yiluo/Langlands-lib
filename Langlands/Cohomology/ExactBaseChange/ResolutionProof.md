# Exact base change computed with arbitrary right resolutions: proof

Author: Worker 1245 (Lean proof and this text).

Module `Langlands.Cohomology.ExactBaseChange.ResolutionProof` proves the published
proposition

`Langlands.Cohomology.ExactBaseChange.ResolutionCompatibilityStatement`

from `Langlands.Cohomology.ExactBaseChange.ResolutionStatement`. The theorem is

`Langlands.Cohomology.ExactBaseChange.resolutionCompatibility :
  ResolutionCompatibilityStatement.{v₁, v₂, v₃, v₄, u₁, u₂, u₃, u₄}`.

Its type is the proposition itself, with the same eight universe parameters in the
same order and no further hypotheses. It proves both conjuncts. The module imports only
`Langlands.Cohomology.ExactBaseChange.ResolutionStatement`. It does not change that
statement or anything it imports. It does not import the flat higher-direct-image
base-change target, either Mumford Euler statement, or anything downstream of them. The
axioms used are `propext`, `Classical.choice` and `Quot.sound`.

All names below are under `Langlands.Cohomology` unless they are Mathlib names. As in
the statement, write `H = HomologicalComplex.homologyFunctor D₂ (ComplexShape.up ℕ) n`,
`I = injectiveResolution A` (Mathlib's chosen injective resolution) and
`t = AcyclicResolution.lift ε (𝟙 A) I.ι`. By definition,
`resolutionComparison F ε n` is `comparison F I t n`, the homology map of `F t`
followed by `(I.isoRightDerivedObj F n).inv`.

## Declarations

The module adds these declarations in the namespace
`Langlands.Cohomology.ExactBaseChange`. The common section variables are those of the
statement: `F₁`, `F₂` additive; `α`, `β` additive, preserving finite limits and
homology; `τ : F₁ ⋙ β ⟶ α ⋙ F₂`; `ε`, `ε'` quasi-isomorphisms; `ψ` and `Φ`.

- `quasiIso_mapResolutionAugmentation α ε`. If `α` is additive and preserves homology
  and `ε` is a quasi-isomorphism, then `mapResolutionAugmentation α ε` is a
  quasi-isomorphism. That map is the inverse of Mathlib's isomorphism
  `singleMapHomologicalComplex` composed with `α.mapHomologicalComplex` applied to `ε`.
  Instance search gives the result, through Mathlib's `quasiIso_comp`,
  `quasiIso_of_isIso` and `HomologicalComplex.quasiIso_map_of_preservesHomology`.
- `map_resolutionComparison_inv_derivedNatTrans ε n`. The map
  `β.map (resolutionComparison F₁ ε n)` followed by
  `inv ((LeftExactHomology.derivedNatTrans β F₁ n).app A)` equals
  `inv ((LeftExactHomology.homologyNatTrans β _ n).app (F₁ K))` followed by
  `resolutionComparison (F₁ ⋙ β) ε n`. Clearing the two inverses reduces this to
  `LeftExactHomology.comparison_comp_derivedHom β F₁ I t n`. This uses that the
  component of `derivedNatTrans` at `A` is by definition `derivedHom β F₁ I n`.
- `resolutionComparison_rightDerived τ ε n`. The map
  `resolutionComparison (F₁ ⋙ β) ε n ≫ (NatTrans.rightDerived τ n).app A` equals
  `H.map ((NatTrans.mapHomologicalComplex τ _).app K) ≫
  resolutionComparison (α ⋙ F₂) ε n`. Mathlib's
  `InjectiveResolution.rightDerived_app_eq τ I n` expands the component of
  `NatTrans.rightDerived τ n` through `I`. The identifications of `I` cancel. The
  result then follows from `NatTrans.mapHomologicalComplex_naturality` for `t`.
- `resolutionComparison_mapResolutionAugmentation hψ n`. Assume
  `mapResolutionAugmentation α ε` is a quasi-isomorphism and
  `hψ : mapResolutionAugmentation α ε ≫ ψ = ε'`. Then
  `resolutionComparison F₂ (mapResolutionAugmentation α ε) n` equals
  `H.map ((F₂.mapHomologicalComplex _).map ψ) ≫ resolutionComparison F₂ ε' n`. This
  is `AcyclicResolution.resolutionComparison_naturality` for `F₂` with the map `ψ`
  lying over the identity of `α A`. Its compatibility hypothesis is `hψ`, after
  simplifying `single₀.map (𝟙 _) ≫ ε'` to `ε'`. The trailing
  `(F₂.rightDerived n).map (𝟙 _)` is removed by `Functor.map_id`.
- `mapHomologicalComplex_comp_eq hΦ`. Under
  `hΦ : ∀ q, Φ.f q = τ.app (K.X q) ≫ F₂.map (ψ.f q)`, the cochain map `Φ` equals the
  composite of `(NatTrans.mapHomologicalComplex τ _).app K`, then
  `(Functor.mapHomologicalComplexCompIso (Iso.refl (α ⋙ F₂)) _).inv.app K`, then
  `(F₂.mapHomologicalComplex _).map ψ`. The proof checks this degreewise: the middle
  map has identity components.
- `resolutionComparison_baseChangeNatTrans τ hψ hΦ n`. This is the first conjunct; see
  below.
- `isIso_baseChangeNatTrans_app_of_acyclic τ hψ hΦ hK hK' n`. This is the second
  conjunct; see below.
- `resolutionCompatibility`, the proof of the proposition. It introduces the data and
  returns the two theorems above.

## First conjunct: the comparison equality

Here `F₁` and `F₂` are only additive. The terms of `K` and `K'` are arbitrary, and
`Φ` need not be a quasi-isomorphism. The proof rewrites the left side
`β.map (resolutionComparison F₁ ε n) ≫ (baseChangeNatTrans τ n).app A` in five steps.

1. `ExactBaseChange.baseChangeNatTrans_app` expands the published component into three
   maps. They are `inv ((derivedNatTrans β F₁ n).app A)`, then
   `(NatTrans.rightDerived τ n).app A`, then
   `compComparison F₂ (Iso.refl (α ⋙ F₂)) A hA n`, where `hA` is the vanishing of the
   positive right derived functors of `α`.
2. `map_resolutionComparison_inv_derivedNatTrans` replaces
   `β.map (resolutionComparison F₁ ε n) ≫ inv (…)` by
   `inv (homologyNatTrans …) ≫ resolutionComparison (F₁ ⋙ β) ε n`.
3. `resolutionComparison_rightDerived` moves `NatTrans.rightDerived τ n` to the
   homology map of `τ` on `K`. This leaves `resolutionComparison (α ⋙ F₂) ε n`.
4. `AcyclicResolution.resolutionComparison_compComparison` is applied with `F := α`,
   `G := F₂` and `e := Iso.refl (α ⋙ F₂)`. Its quasi-isomorphism instance comes from
   `quasiIso_mapResolutionAugmentation`. It turns
   `resolutionComparison (α ⋙ F₂) ε n ≫ compComparison …` into the homology map of
   `(mapHomologicalComplexCompIso (Iso.refl _) _).inv.app K` followed by
   `resolutionComparison F₂ (mapResolutionAugmentation α ε) n`.
5. `resolutionComparison_mapResolutionAugmentation hψ` replaces the last comparison by
   `H.map (F₂ ψ) ≫ resolutionComparison F₂ ε' n`.

The left side is now `inv (homologyNatTrans …)` followed by `H` of three cochain maps
and `resolutionComparison F₂ ε' n`. Rewriting `Φ` with `mapHomologicalComplex_comp_eq hΦ`
and expanding `H.map` of the composite with `Functor.map_comp` makes both sides equal
up to associativity.

## Second conjunct: the isomorphism criterion

Assume in addition `[PreservesFiniteLimits F₁]`, `[PreservesFiniteLimits F₂]`, the
termwise acyclicity hypotheses `hK` for `K` and `hK'` for `K'`, and `QuasiIso Φ`. Fix
`n`.

- The published theorem `acyclicResolutionComparisonStatement`, from module
  `Langlands.Cohomology.AcyclicResolution.ComparisonProof`, is applied to `F₁`, `ε`,
  `hK`, `injectiveResolution A`, the lift `lift ε (𝟙 A) _` and
  `AcyclicResolution.comp_lift_id`. Its second component says that
  `resolutionComparison F₁ ε n` is an isomorphism. The same theorem applied to `F₂`,
  `ε'` and `hK'` shows that `resolutionComparison F₂ ε' n` is an isomorphism. This
  module is already in the import closure of the statement.
- `H.map Φ` is `HomologicalComplex.homologyMap Φ n`, which is an isomorphism by
  `QuasiIso Φ`.
- `inv (homologyNatTrans …)` is an isomorphism. The instance
  `LeftExactHomology.isIso_homologyNatTrans` applies because `β` preserves homology.

By the first conjunct,
`β.map (resolutionComparison F₁ ε n) ≫ (baseChangeNatTrans τ n).app A` is a composite
of isomorphisms. Its first factor `β.map (resolutionComparison F₁ ε n)` is an
isomorphism. `IsIso.of_isIso_comp_left` then shows that
`(baseChangeNatTrans τ n).app A` is an isomorphism. This covers every `n`, including
`n = 0`. The transformation is the published `baseChangeNatTrans τ n`, the same one as
in the first conjunct.

## Scope and provenance

This is a proof of an internal compatibility proposition about the published
constructions `ExactBaseChange.baseChangeNatTrans`, `AcyclicResolution.resolutionComparison`,
`AcyclicResolution.mapResolutionAugmentation` and `LeftExactHomology.homologyNatTrans`.
None of these is redefined. No comparison map is assumed invertible, and no unproved
Library proposition is assumed. The only external result used for the criterion is the
proved theorem `acyclicResolutionComparisonStatement`.

The proposition is motivated by Stacks Project, Lemma 02N7 (tag
`lemma-base-change-map-flat-case`, `cohomology.tex` lines 2955–3032 at commit
`a04446e57ec1fbc252a871afcec7752fb2807b14`). The provenance is described in the
statement's Markdown. The source does not state this four-category equality or the
criterion, and the proof follows the published Lean constructions rather than the
source's argument. This module does not identify `baseChangeNatTrans` with the
source's derived-category morphism. It does not prove the geometric base change
theorem or any Euler statement.

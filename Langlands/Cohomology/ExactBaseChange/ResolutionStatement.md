# Exact base change computed with arbitrary right resolutions

Authors: Worker 894 (Lean statement and this text); Worker 360 and Worker 1098
(joint specification of the common interface and of the split into a comparison
equality and an acyclic isomorphism criterion).

Module `Langlands.Cohomology.ExactBaseChange.ResolutionStatement`. It contains one
declaration, the `Prop`-valued definition

`Langlands.Cohomology.ExactBaseChange.ResolutionCompatibilityStatement`.

The module states a proposition and does not prove it. Nothing in the Library
derives anything from it, and importing it supplies no proved fact. It is a derived,
internal assertion motivated by Stacks Project, Lemma 02N7 (see "Provenance"). It is
not a statement of that lemma.

## Published declarations used

All names below are under `Langlands.Cohomology` unless they are Mathlib names.

- `ExactBaseChange.baseChangeNatTrans τ n : F₁.rightDerived n ⋙ β ⟶ α ⋙ F₂.rightDerived n`
  (module `Langlands.Cohomology.ExactBaseChange`), defined as
  `inv (LeftExactHomology.derivedNatTrans β F₁ n) ≫ NatTrans.rightDerived τ n ≫
  ExactBaseChange.compComparisonNatTrans α F₂ n`. This is the transformation the
  proposition is about. It is used unchanged, and no replacement comparison is
  defined.
- `AcyclicResolution.resolutionComparison F ε n : Hⁿ(F K) ⟶ (F.rightDerived n).obj A`
  (module `Langlands.Cohomology.AcyclicResolution.Comparison`). For an additive `F`
  and a quasi-isomorphism `ε : A[0] ⟶ K` it is the homology map of `F` applied to the
  lift of `ε` into Mathlib's chosen injective resolution of `A`, followed by Mathlib's
  identification of `Rⁿ F A` with the homology of `F` of that resolution. Its source is
  `(F.mapHomologicalComplex _ ⋙ HomologicalComplex.homologyFunctor _ _ n).obj K`. It
  needs the instance `[QuasiIso ε]`, so the two resolution augmentations below
  carry that instance.
- `AcyclicResolution.mapResolutionAugmentation α ε : (α A)[0] ⟶ α K` (module
  `Langlands.Cohomology.AcyclicResolution.Composition`): Mathlib's identification
  of `α` applied to `A[0]` with `(α A)[0]`, followed by `α` applied to `ε`.
- `LeftExactHomology.homologyNatTrans β (ComplexShape.up ℕ) n :
  β.mapHomologicalComplex _ ⋙ homologyFunctor D₂ _ n ⟶ homologyFunctor D₁ _ n ⋙ β`
  (module `Langlands.Cohomology.LeftExactHomology`), the canonical map
  `Hⁿ(β L) ⟶ β(Hⁿ L)`. It is an isomorphism by the instance
  `LeftExactHomology.isIso_homologyNatTrans` because `β` preserves homology. That is
  why its inverse can be written.

The module imports only `Langlands.Cohomology.ExactBaseChange` and
`Langlands.Cohomology.AcyclicResolution.Composition`. Neither the flat
higher-direct-image base-change target nor either Mumford Euler statement is in its
import closure. No published Lean or Markdown file is changed.

## The common data

The proposition quantifies, in this order, over:

- abelian categories `C₁ : Type u₁`, `C₂ : Type u₂`, `D₁ : Type u₃`, `D₂ : Type u₄`,
  with morphism universes `v₁ v₂ v₃ v₄`. The eight universes are independent. `C₁`
  and `C₂` have injective resolutions (`HasInjectiveResolutions`), so that Mathlib's
  `Functor.rightDerived` is defined for functors out of them;
- additive functors `F₁ : C₁ ⥤ D₁` and `F₂ : C₂ ⥤ D₂`, with no other hypotheses;
- functors `α : C₁ ⥤ C₂` and `β : D₁ ⥤ D₂` that are additive, preserve finite limits
  and preserve homology (`[Additive] [PreservesFiniteLimits] [PreservesHomology]`).
  These are exactly the instances that `baseChangeNatTrans` requires;
- an arbitrary natural transformation `τ : F₁ ⋙ β ⟶ α ⋙ F₂`;
- an object `A : C₁` and cochain complexes `K : CochainComplex C₁ ℕ` and
  `K' : CochainComplex C₂ ℕ`;
- right resolutions `ε : (CochainComplex.single₀ C₁).obj A ⟶ K` and
  `ε' : (CochainComplex.single₀ C₂).obj (α.obj A) ⟶ K'`, each with a `[QuasiIso _]`
  instance. Nothing is assumed about the terms of `K` or `K'` here: they need not be
  injective or acyclic;
- a cochain map `ψ : (α.mapHomologicalComplex (ComplexShape.up ℕ)).obj K ⟶ K'`,
  together with the hypothesis
  `AcyclicResolution.mapResolutionAugmentation α ε ≫ ψ = ε'`, which says that `ψ` is
  compatible with the augmentations;
- a cochain map
  `Φ : (β.mapHomologicalComplex _).obj ((F₁.mapHomologicalComplex _).obj K) ⟶
  (F₂.mapHomologicalComplex _).obj K'`, together with the hypothesis
  `∀ q : ℕ, Φ.f q = τ.app (K.X q) ≫ F₂.map (ψ.f q)`.

Every complex and functor here is the actual Mathlib object. `Φ` is part of the data,
and its components are fixed by the last hypothesis. It is quantified rather than
constructed because a cochain map has to be given together with its compatibility
with the differentials, and that compatibility is a consequence of the naturality of
`τ` and the fact that `ψ` is a cochain map. Since the components are determined, there
is at most one such `Φ`. No comparison isomorphism and no choice of injective
resolution is part of the data.

After the common data and the two compatibility hypotheses, the proposition is the
conjunction of the two conclusions below.

## First conclusion: the comparison equality

For every `n : ℕ`, including `n = 0`:

```lean
β.map (AcyclicResolution.resolutionComparison F₁ ε n) ≫
    (ExactBaseChange.baseChangeNatTrans τ n).app A =
  inv ((LeftExactHomology.homologyNatTrans β (ComplexShape.up ℕ) n).app
      ((F₁.mapHomologicalComplex (ComplexShape.up ℕ)).obj K)) ≫
    (HomologicalComplex.homologyFunctor D₂ (ComplexShape.up ℕ) n).map Φ ≫
      AcyclicResolution.resolutionComparison F₂ ε' n
```

Both sides are morphisms `β(Hⁿ(F₁ K)) ⟶ (F₂.rightDerived n).obj (α.obj A)`. On the
left, `β` of the comparison `Hⁿ(F₁ K) ⟶ Rⁿ F₁ A` is followed by the component at `A` of
the published base change transformation. On the right, `β(Hⁿ(F₁ K))` is first
identified with `Hⁿ(β(F₁ K))` by the inverse of `homologyNatTrans`. This is followed by
the homology of `Φ`, landing in `Hⁿ(F₂ K')`, and then by the comparison
`Hⁿ(F₂ K') ⟶ Rⁿ F₂ (α A)` of the resolution `ε'`.

The equality is asserted with no further hypotheses. In particular, it is not assumed
that `F₁` or `F₂` preserves finite limits, that the terms of `K` or `K'` are acyclic,
that `Φ` is a quasi-isomorphism, or that either comparison map is invertible.

## Second conclusion: the isomorphism criterion

For the same data, assume in addition:

- `[PreservesFiniteLimits F₁]` and `[PreservesFiniteLimits F₂]` (left exactness);
- `∀ q r : ℕ, IsZero ((F₁.rightDerived (r + 1)).obj (K.X q))`, that is, every term of
  `K` is `F₁`-acyclic;
- `∀ q r : ℕ, IsZero ((F₂.rightDerived (r + 1)).obj (K'.X q))`, that is, every term
  of `K'` is `F₂`-acyclic;
- `QuasiIso Φ`.

Then `∀ n : ℕ, IsIso ((ExactBaseChange.baseChangeNatTrans τ n).app A)`. The
transformation is the same published one as in the equality.

The two finite-limit instances are bound inside the second conjunct, so they do not
affect the first. No hypothesis that a comparison map is invertible appears, and no
unproved Library proposition is assumed. In particular, the criterion applies when
every component `Φ.f q` is an isomorphism. In that case `Φ` is an isomorphism of
complexes by Mathlib's `HomologicalComplex.Hom.isIso_of_components`, and hence a
quasi-isomorphism by Mathlib's instance `quasiIso_of_isIso`.

## Why these hypotheses

This section explains the intended reading. It is not a proof, and no part of it is
proved in this module.

- The equality says that the published transformation, which is built from Mathlib's
  chosen injective resolutions, can be computed from any pair of right resolutions
  connected by an augmentation-compatible map. The informally expected route
  combines four ingredients. The first is the component formula
  `ExactBaseChange.baseChangeNatTrans_app`. The second is the compatibility of
  `LeftExactHomology.derivedNatTrans` with the homology maps. The third is
  `AcyclicResolution.resolutionComparison_compComparison`, which needs `α` applied
  to `ε` to be a quasi-isomorphism; that follows from the exactness of `α`. The
  fourth is the naturality of `resolutionComparison` along `ψ` over the identity of
  `α A`. None of these steps uses left exactness of `F₁` or `F₂` or acyclicity. This
  is why the equality is stated without those hypotheses.
- The criterion is a formal consequence of the equality. Deriving it is part of
  the later proof task. Under left exactness and termwise acyclicity, the ordinary
  acyclic-resolution comparison theorem makes both resolution comparisons
  isomorphisms. That theorem is
  `Langlands.Cohomology.acyclicResolutionComparisonStatement`, a proof of
  `AcyclicResolutionComparisonStatement` in the Library module
  `Langlands.Cohomology.AcyclicResolution.ComparisonProof`; together with
  `AcyclicResolution.resolutionComparison_eq` it applies to `resolutionComparison`.
  That module is in this module's transitive import closure, but the proposition
  does not refer to it. Since `β` preserves homology, `homologyNatTrans` is
  invertible, and `QuasiIso Φ` makes the homology map of `Φ` invertible.
  Cancelling the invertible factor `β.map (resolutionComparison F₁ ε n)` in the
  equality then gives the conclusion. The criterion is stated as a separate
  conclusion so that it does not depend on any chosen comparison isomorphism.

## Provenance

Stacks Project, Cohomology of Sheaves, section "The base change map"
(`section-base-change-map`), Lemma 02N7 (`lemma-base-change-map-flat-case`) and its
proof, `cohomology.tex` lines 2955–3032 at commit
`a04446e57ec1fbc252a871afcec7752fb2807b14`. The file's SHA-256 is
`fa9747d0082afbf8b09244dcc6c260f8a122e5e3b4a3c69e2273506d76e18a42`. It belongs to the
registered source `stacks-flasque-affine-vanishing-kunneth-a04446e5`, whose folder
SHA-256 is `af02e6f0aff875e216f1e0fde58f6baad3eedeb6b82799a8d6c91ff68cccaa3a`.

The source considers a commutative square of ringed spaces `f : X → S`,
`f' : X' → S'`, `g : S' → S`, `g' : X' → X` with `g` and `g'` flat, and a bounded
below complex `F` on `X`. The paragraph before the lemma uses the exactness of flat
pullback, so `g^*` needs no deriving. The proof chooses injective resolutions
`F → I` and `g'^* F → J`. It lifts the adjunction map `F → g'_* g'^* F → g'_* J` to a
map `β : I → g'_* J`, which is unique up to homotopy. It pushes `β` down to
`f_* I → f_* g'_* J = g_* f'_* J` and takes the adjoint map of complexes
`g^* f_* I → f'_* J`. Lines 3027–3031 identify this map of complexes and note that
it is unique up to homotopy, since the only choice was `β`.

The abstract roles are `F₁ = f_*`, `F₂ = f'_*`, `β = g^*`, `α = g'^*`, and `τ` the
degree-zero base change map `g^* f_* ⟶ f'_* g'^*`. Under this dictionary, the source's
cochain map `g^* f_* I → f'_* J` has the shape of `Φ`: degreewise, it is `τ` at
`I^q` followed by `f'_*` of the map `g'^* I^q → J^q` adjoint to `β`. The map
`g'^* I → J` plays the role of `ψ`, and the compatibility of `β` with the
adjunction map plays the role of the augmentation condition. In this sense the
source motivates comparing the published degreewise transformation with such a
cochain map. Here this is done for arbitrary right resolutions instead of injective
ones, and for arbitrary exact additive functors `α` and `β` instead of flat
pullbacks; no flatness notion appears.

The source does not state the four-category comparison equality or the
acyclic-resolution isomorphism criterion. Both are internal and derived from the
published constructions `baseChangeNatTrans`, `resolutionComparison`,
`mapResolutionAugmentation` and `homologyNatTrans`. The criterion is the formal
consequence of the equality and the ordinary acyclic-resolution comparison theorem.
This module does not claim or prove an identification of `baseChangeNatTrans` with
the source's morphism `g^* Rf_* F → R f'_* g'^* F` in `D⁺(S')`. It also does not
prove the geometric base change theorem or the proposition itself.

The proposition was specified for the parent task
`5b778a75-e74b-4ae4-9232-6735e3eefa47` by Worker 360 and Worker 1098. A separate
task is to prove it.

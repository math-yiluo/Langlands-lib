# Base change of right derived functors along exact functors

Authors: Worker 950 and Worker 1098 (construction audit).

Module `Langlands.Cohomology.ExactBaseChange`. It defines, for a square of additive
functors between abelian categories whose two horizontal functors are exact, the
induced degreewise natural transformation on right derived functors, together with
its component formula. It contains two definitions and two component lemmas, all
in the namespace `Langlands.Cohomology.ExactBaseChange`. There are no hypotheses
beyond those listed below and no proof holes.

This is an internal, derived construction: an abstract four-category version of
the degreewise form of the base change map of Stacks Project, Cohomology of
Sheaves, Lemma 02N7 (see "Provenance"). It is not a verbatim statement of that
source. The module proves nothing about the transformation beyond its naturality
(which is part of the data of a natural transformation) and its component formula.
In particular it does not show that the transformation is an isomorphism, and it
does not prove any compatibility with resolutions, with pasting of squares, or with
other base change constructions.

## Setting

Throughout:

- `C₁`, `C₂`, `D₁`, `D₂` are abelian categories, with independent object universes
  `u₁ u₂ u₃ u₄` and morphism universes `v₁ v₂ v₃ v₄`;
- `C₁` and `C₂` have injective resolutions (`HasInjectiveResolutions`), so that
  Mathlib's right derived functors `Functor.rightDerived` of functors out of them
  are defined;
- `Rⁿ F` denotes Mathlib's `F.rightDerived n`.

The published declarations used are:

- `Langlands.Cohomology.LeftExactHomology.derivedNatTrans Φ F n :
  (F ⋙ Φ).rightDerived n ⟶ F.rightDerived n ⋙ Φ` (module
  `Langlands.Cohomology.LeftExactHomology`), defined for additive `F` and additive
  `Φ` preserving finite limits, and an isomorphism by the instance
  `LeftExactHomology.isIso_derivedNatTrans` when `Φ` also preserves homology;
- `Langlands.Cohomology.AcyclicResolution.compComparison G e A hA n :
  (H.rightDerived n).obj A ⟶ (G.rightDerived n).obj (F.obj A)` (module
  `Langlands.AlgebraicGeometry.Modules.PushforwardComparison`), for
  `e : F ⋙ G ≅ H`, `F` additive and preserving finite limits, `G` and `H`
  additive, and `hA : ∀ q, IsZero ((F.rightDerived (q + 1)).obj A)`;
- `Langlands.Cohomology.AcyclicResolution.compComparison_naturality` (module
  `Langlands.AlgebraicGeometry.Modules.CohomologyBaseChange`), the naturality of
  `compComparison` in `A`;
- `Langlands.AlgebraicGeometry.Modules.DerivedSections.isZero_rightDerived_succ_of_preservesHomology`
  (module `Langlands.AlgebraicGeometry.Modules.HigherDirectImageOpenRestriction`):
  for an additive functor `F` preserving homology and any object `N`,
  `IsZero ((F.rightDerived (q + 1)).obj N)`. Despite its namespace, it is a
  statement about arbitrary abelian categories;
- Mathlib's `NatTrans.rightDerived` (`CategoryTheory/Abelian/RightDerived.lean`).

## `compComparisonNatTrans`

Assumptions: `α : C₁ ⥤ C₂` is additive, preserves finite limits and preserves
homology (`[α.Additive] [PreservesFiniteLimits α] [α.PreservesHomology]`);
`F₂ : C₂ ⥤ D₂` is additive. For `n : ℕ`,

`compComparisonNatTrans α F₂ n : (α ⋙ F₂).rightDerived n ⟶ α ⋙ F₂.rightDerived n`

has component at `A : C₁`

`compComparison F₂ (Iso.refl (α ⋙ F₂)) A
  (fun q => isZero_rightDerived_succ_of_preservesHomology α A q) n`,

that is, the comparison `Rⁿ(α ⋙ F₂) A ⟶ Rⁿ F₂ (α A)` for the identity isomorphism of
`α ⋙ F₂`, where the vanishing of `R^{q+1} α A` comes from the exactness of `α`. Its
naturality is `compComparison_naturality F₂ (Iso.refl (α ⋙ F₂)) u _ _ n`.

The lemma `compComparisonNatTrans_app` states this component formula; it holds by
`rfl`.

## `baseChangeNatTrans`

Assumptions: `F₁ : C₁ ⥤ D₁` and `F₂ : C₂ ⥤ D₂` are additive; `α : C₁ ⥤ C₂` and
`β : D₁ ⥤ D₂` are additive, preserve finite limits and preserve homology. Let
`τ : F₁ ⋙ β ⟶ α ⋙ F₂` be a natural transformation. For `n : ℕ`,

`baseChangeNatTrans τ n : F₁.rightDerived n ⋙ β ⟶ α ⋙ F₂.rightDerived n`

is defined as the composite

`inv (LeftExactHomology.derivedNatTrans β F₁ n) ≫ NatTrans.rightDerived τ n ≫
  compComparisonNatTrans α F₂ n`,

of natural transformations

`Rⁿ F₁ ⋙ β ⟶ Rⁿ(F₁ ⋙ β) ⟶ Rⁿ(α ⋙ F₂) ⟶ α ⋙ Rⁿ F₂`.

The inverse exists by the instance `LeftExactHomology.isIso_derivedNatTrans`, since
`β` preserves homology. The finite-limit and homology hypotheses on `α` are used
only by `compComparisonNatTrans`, and those on `β` only by the first factor.

The lemma `baseChangeNatTrans_app` gives the component at `A : C₁`:

`(baseChangeNatTrans τ n).app A =
  inv ((LeftExactHomology.derivedNatTrans β F₁ n).app A) ≫
    (NatTrans.rightDerived τ n).app A ≫
      compComparison F₂ (Iso.refl (α ⋙ F₂)) A
        (fun q => isZero_rightDerived_succ_of_preservesHomology α A q) n`.

Proof: unfold the definition, split the components of the composite with
`NatTrans.comp_app`, and rewrite the component of the inverse with Mathlib's
`NatIso.isIso_inv_app`; the last factor is then `compComparisonNatTrans_app`, by
`rfl`.

## Provenance

Stacks Project, Cohomology of Sheaves, section "The base change map", Lemma 02N7
(`lemma-base-change-map-flat-case`), `cohomology.tex` lines 2953–3032 at commit
`a04446e57ec1fbc252a871afcec7752fb2807b14` (registered source
`stacks-flasque-affine-vanishing-kunneth-a04446e5`). For a commutative square of
ringed spaces with `g` and `g'` flat, the source constructs a map
`g^* Rf_* F ⟶ R f'_* g'^* F` in `D⁺(S')` on cochain level: choose injective
resolutions `F ⟶ I` and `g'^* F ⟶ J`, lift the adjunction unit
`F ⟶ g'_* g'^* F ⟶ g'_* J` to a map `I ⟶ g'_* J`, push it forward along `f`, and
take its adjoint `g^* f_* I ⟶ f'_* J`. Flatness enters there through exactness of
`g^*` and `g'^*`: they need not be derived, and `g'_*` preserves injectives
(`lemma-pushforward-injective-flat`). The live tag page, checked 2026-11-02, has two
comments: #5457 observes that the proof uses flatness of `g'` only, and #5675 replies
that flatness of `g` is what makes `g^* f_* I` compute `Lg^* Rf_* F`. Here both roles
are played by explicit exactness hypotheses on `α` and `β`.

The construction here is a degreewise, single-object analogue, built from existing
right derived functors instead of an explicit cochain map. The roles are: `F₁` and
`F₂` are the direct images, `β` and `α` the exact pullbacks on the bases and on the
sources, and `τ` the degree-zero base change map `g^* f_* ⟶ f'_* g'^*`. Exactness of
`β` turns `Rⁿ F₁ ⋙ β` into `Rⁿ(F₁ ⋙ β)` (this replaces applying `g^*` to the complex
`f_* I`); `NatTrans.rightDerived τ n` applies the degree-zero map to an injective
resolution; and exactness of `α` turns `Rⁿ(α ⋙ F₂) A` into `Rⁿ F₂ (α A)`, because `α`
of an injective resolution `I` of `A` is a resolution of `α A`, compared with an
injective resolution of `α A` (the analogue of the adjoint map `g'^* I ⟶ J`). The
abstract four-category formulation is an internal generalization: it is not stated
in the source, and no identification of this transformation with the
source's derived-category map is claimed or proved here. The hypotheses are exactly
the explicit instances listed above; no flatness notion appears.

The construction and its interfaces were specified by Worker 360 for parent task
`5b778a75-e74b-4ae4-9232-6735e3eefa47`, after a joint interface audit with
Worker 1098.

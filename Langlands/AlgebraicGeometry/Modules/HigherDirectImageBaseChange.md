# Base change transformations for higher direct images along exact pullbacks

Authors: Worker 950 and Worker 1098 (construction audit).

Module `Langlands.AlgebraicGeometry.Modules.HigherDirectImageBaseChange`. For a
commutative square of schemes it bundles the existing degree-zero base change
morphisms into a natural transformation, and, when the two pullbacks are given to
preserve finite limits, defines the induced base change transformation on higher
direct images in every degree. All declarations are in the namespace
`Langlands.AlgebraicGeometry.Modules.DerivedSections`. There are no hypotheses
beyond those listed below and no proof holes.

The transformation on higher direct images is the specialization of the abstract
`Langlands.Cohomology.ExactBaseChange.baseChangeNatTrans` (module
`Langlands.Cohomology.ExactBaseChange`, whose Markdown describes that construction
and its provenance). It is a derived construction, the degreewise analogue of
Stacks Project, Cohomology of Sheaves, Lemma 02N7 (see "Provenance"). The module
proves nothing about it beyond naturality and the component formula. In particular
it does **not** prove that pullback along a flat morphism preserves finite limits
(exactness is an explicit instance hypothesis here), that the transformation is an
isomorphism, that it is compatible with resolutions or with pasting of squares, or
that it agrees with any other base change construction.

## Setting

`X Y X' Y' : Scheme.{u}` for an arbitrary universe `u`, with morphisms
`f : X ⟶ Y`, `g : Y' ⟶ Y`, `f' : X' ⟶ Y'`, `g' : X' ⟶ X` and a proof
`w : g' ≫ f = f' ≫ g` that the square commutes:

```text
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

No further assumption is made on the square (it need not be cartesian, and no
morphism need be flat, quasi-compact or separated) or on the modules. Write `h_*` for
Mathlib's `Scheme.Modules.pushforward h`, `h^*` for Mathlib's
`Scheme.Modules.pullback h`, and `Rⁿ h_*` for the Library's
`DerivedSections.higherDirectImage h n`, which is by definition
`(Scheme.Modules.pushforward h).rightDerived n` (module
`Langlands.AlgebraicGeometry.Modules.DerivedSections`).

The degree-zero morphism is the Library's
`DerivedSections.pushforwardBaseChange g f f' g' w M : g^* f_* M ⟶ f'_* g'^* M`
(module `Langlands.AlgebraicGeometry.Modules.DerivedRestriction`), defined as the
adjunct, under `g^* ⊣ g_*` (Mathlib's `Scheme.Modules.pullbackPushforwardAdjunction`),
of

`f_*(η_M) ≫ (pushforwardSquareIso g f f' g' w).hom.app (g'^* M) :
f_* M ⟶ f_* g'_* g'^* M ⟶ g_* f'_* g'^* M`,

where `η` is the unit of `g'^* ⊣ g'_*` and `pushforwardSquareIso g f f' g' w :
g'_* ⋙ f_* ≅ f'_* ⋙ g_*` is the comparison of pushforwards around the square.

## `pushforwardBaseChange_naturality`

For `u : M ⟶ N` in `X.Modules`,

`g^*.map (f_*.map u) ≫ pushforwardBaseChange g f f' g' w N =
  pushforwardBaseChange g f f' g' w M ≫ f'_*.map (g'^*.map u)`.

The `@[reassoc]` attribute also generates `pushforwardBaseChange_naturality_assoc`.

Proof. Unfold both base change morphisms and move `g^*.map (f_*.map u)` and
`f'_*.map (g'^*.map u)` inside the adjunction bijection with Mathlib's
`Adjunction.homEquiv_naturality_left_symm` and
`Adjunction.homEquiv_naturality_right_symm`. It remains to show

`f_*.map u ≫ f_*.map (η_N) ≫ σ.app (g'^* N) =
  (f_*.map (η_M) ≫ σ.app (g'^* M)) ≫ g_*.map (f'_*.map (g'^*.map u))`

for `σ = (pushforwardSquareIso g f f' g' w).hom`. This follows by rewriting with
the naturality of the unit `η` at `u` and the naturality of `σ` at `g'^*.map u`.

## `pushforwardBaseChangeNatTrans`

`pushforwardBaseChangeNatTrans g f f' g' w : f_* ⋙ g^* ⟶ g'^* ⋙ f'_*` has component
`pushforwardBaseChange g f f' g' w M` at `M : X.Modules`; its naturality is
`pushforwardBaseChange_naturality`. The lemma `pushforwardBaseChangeNatTrans_app`
states the component formula, by `rfl`.

## `higherDirectImageBaseChangeNatTrans`

Additional assumptions: the explicit instances

`[PreservesFiniteLimits (Scheme.Modules.pullback g)]` and
`[PreservesFiniteLimits (Scheme.Modules.pullback g')]`.

For `n : ℕ`,

`higherDirectImageBaseChangeNatTrans g f f' g' w n :
  higherDirectImage f n ⋙ g^* ⟶ g'^* ⋙ higherDirectImage f' n`

is `ExactBaseChange.baseChangeNatTrans (pushforwardBaseChangeNatTrans g f f' g' w) n`,
the abstract construction for `C₁ = X.Modules`, `C₂ = X'.Modules`, `D₁ = Y.Modules`,
`D₂ = Y'.Modules`, `F₁ = f_*`, `F₂ = f'_*`, `α = g'^*`, `β = g^*` and
`τ = pushforwardBaseChangeNatTrans g f f' g' w`. That is, it is the composite

`inv (LeftExactHomology.derivedNatTrans g^* f_* n) ≫
  NatTrans.rightDerived (pushforwardBaseChangeNatTrans g f f' g' w) n ≫
    ExactBaseChange.compComparisonNatTrans g'^* f'_* n`

of `Rⁿ f_* ⋙ g^* ⟶ Rⁿ(f_* ⋙ g^*) ⟶ Rⁿ(g'^* ⋙ f'_*) ⟶ g'^* ⋙ Rⁿ f'_*`.

The other hypotheses of the abstract construction are found by instance search:
the module categories of schemes are abelian with injective resolutions, the
pushforwards and pullbacks are additive, and the pullbacks, being left adjoints,
preserve finite colimits (Mathlib, `AlgebraicGeometry/Modules/Sheaf.lean`). From
finite limits and finite colimits Mathlib's `Functor.preservesHomologyOfExact`
(`Algebra/Homology/ShortComplex/PreservesHomology.lean`) gives preservation of
homology.

The lemma `higherDirectImageBaseChangeNatTrans_app` gives the component at
`M : X.Modules`:

`(higherDirectImageBaseChangeNatTrans g f f' g' w n).app M =
  inv ((LeftExactHomology.derivedNatTrans g^* f_* n).app M) ≫
    (NatTrans.rightDerived (pushforwardBaseChangeNatTrans g f f' g' w) n).app M ≫
      AcyclicResolution.compComparison f'_* (Iso.refl (g'^* ⋙ f'_*)) M
        (fun q => isZero_rightDerived_succ_of_preservesHomology _ M q) n`.

It is `ExactBaseChange.baseChangeNatTrans_app` for this instance.

## Provenance

Stacks Project, Cohomology of Sheaves, section "The base change map", Lemma 02N7
(`lemma-base-change-map-flat-case`), `cohomology.tex` lines 2953–3032 at commit
`a04446e57ec1fbc252a871afcec7752fb2807b14` (registered source
`stacks-flasque-affine-vanishing-kunneth-a04446e5`). For a commutative square of
ringed spaces with `g` and `g'` flat, the source constructs the base change map
`g^* Rf_* F ⟶ R f'_* g'^* F` in `D⁺(S')` from injective resolutions and adjunction.
Flatness enters there only through the exactness of `g^*` and `g'^*` (see also the
two comments on the tag page, summarized in the Markdown of
`Langlands.Cohomology.ExactBaseChange`).

The present construction replaces flatness by the explicit finite-limit
instances on the two pullbacks and works degreewise on single modules, giving
`g^* (Rⁿ f_* M) ⟶ Rⁿ f'_* (g'^* M)` through the abstract construction
described in the Markdown of `Langlands.Cohomology.ExactBaseChange`. Its degree-zero
input is the Library's existing `pushforwardBaseChange`, the unit-and-adjunction map
that also appears in the source's proof. The degreewise formulation, the use of
existing right derived functors, and the explicit exactness instances are
internal choices; the source states no such degreewise lemma, and no
identification with the source's derived-category map is proved here.

The construction and its interfaces were specified by Worker 360 for parent task
`5b778a75-e74b-4ae4-9232-6735e3eefa47`, after a joint interface audit with
Worker 1098.

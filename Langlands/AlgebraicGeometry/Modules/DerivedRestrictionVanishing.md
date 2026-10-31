# Higher direct images of flasque modules and the square vanishing condition

Author: Worker 727.

Module `Langlands.AlgebraicGeometry.Modules.DerivedRestrictionVanishing`,
namespace `Langlands.AlgebraicGeometry.Modules.DerivedSections`. It proves:

1. Higher direct images of flasque modules vanish along every morphism of
   schemes.
2. Consider a commutative square `gZ ≫ i = i' ≫ g` with closed immersions `i`
   and `i'`. If the higher direct images of `N` along `gZ` vanish, then so do
   those of `i'_* N` along `g`.
3. Consequently, the third vanishing hypothesis of the Library's
   `derivedRestrictionMap_comp_derivedBaseChangeMap` and
   `restrictionCohomologyMap_comp_baseChangeMap` (module
   `Langlands.AlgebraicGeometry.Modules.DerivedRestriction`) can be dropped.

Everything is proved in the file, with no hypotheses beyond those in the
signatures and no proof holes.

## Conventions

All schemes are in one universe `u`. Write `h_*`, `h^*` for Mathlib's
`Scheme.Modules.pushforward h`, `Scheme.Modules.pullback h`, and
`R^{q+1} h_*` for the Library's `higherDirectImage h (q + 1)` (the right
derived functors of `h_*`). A module `F` is flasque when
`TopCat.Presheaf.IsFlasque F.presheaf` holds.

## Section `Flasque`

Let `f : X ⟶ Y` be an arbitrary morphism of schemes.

- `epi_pushforward_map_of_isFlasque f hS`: for a short exact sequence
  `S : 0 ⟶ F ⟶ I ⟶ Q ⟶ 0` of `𝒪_X`-modules with `F` flasque, `f_* I ⟶ f_* Q` is
  an epimorphism. Proof: for every open `V` of `Y`, Mathlib's
  `TopCat.Sheaf.IsFlasque.epi_of_shortExact` gives surjectivity of the
  sections over `f⁻¹ V`; this is local surjectivity, and the Library's
  `epi_of_isLocallySurjective` concludes.
- `isZero_higherDirectImage_of_isFlasque f q F`: for flasque `F`,
  `R^{q+1} f_* F = 0`. Proof: dimension shifting along the Library's
  `0 ⟶ F ⟶ I ⟶ I / F ⟶ 0` with `I` injective (`injectiveSc`), using the
  connecting morphisms of the Library's right-derived long exact sequence
  (`DerivedPlus.rightDerivedδ`, `epi_rightDerivedδ_of_isZero`,
  `rightDerived_map_comp_δ`). Here `I / F` is again flasque (the Library's
  `isFlasque_cokernel`). Degree one uses the previous lemma. The argument is
  the one used for global sections in the Library's
  `isZero_cohomology_succ_of_isFlasque`, with `f_*` in place of global sections.
- `isZero_higherDirectImage_pushforward_injective f h J q`: for an injective
  `J` on `Z` and any `h : Z ⟶ X`, `R^{q+1} f_*(h_* J) = 0`. The Library's
  `isFlasque_of_injective` and `isFlasque_pushforward` show that `h_* J` is
  flasque.

## Section `Square`

Data: `g : X' ⟶ X`, closed immersions `i : Z ⟶ X` and `i' : Z' ⟶ X'`,
`gZ : Z' ⟶ Z` and `sq : gZ ≫ i = i' ≫ g`.

- `isZero_higherDirectImage_pushforward_of_square g i i' gZ sq N hN q`:
  if `R^{q+1} gZ_* N = 0` for all `q`, then `R^{q+1} g_*(i'_* N) = 0`. Proof:
  the Library's `compComparison` for `i'_* ⋙ g_* ≅ gZ_* ⋙ i_*` (the inverse of
  `pushforwardSquareIso`) is an isomorphism
  `R^{q+1}(gZ_* ⋙ i_*) N ≅ R^{q+1} g_*(i'_* N)` by the Library's
  `isIso_compComparison`. Its hypotheses are `R^{q+1} i'_* N = 0` (closed
  immersion) and the previous section for pushforwards of injectives. The
  source vanishes by `isZero_rightDerived_comp_of_preservesHomology`, because
  `i_*` preserves homology.
- `isZero_higherDirectImage_pullbackSquare`: the hypothesis on `gZ^* i^* M`
  transfers to `i'^* g^* M` along `pullbackSquareIso`.
- `isZero_higherDirectImage_pushforward_pullbackSquare g i i' gZ sq M hMZ q`:
  from `R^{q+1} gZ_*(gZ^* i^* M) = 0` it follows that
  `R^{q+1} g_*(i'_* i'^* g^* M) = 0`.

## Section `BaseChange`

With `φ : R ⟶ R'`, `f : X ⟶ Spec R`, `f' : X' ⟶ Spec R'`,
`w : g ≫ f = f' ≫ Spec.map φ` and the square above:

- `derivedRestrictionMap_comp_derivedBaseChangeMap_of_vanishing φ f f' g w i i' gZ sq M hM hMZ`
  is the Library's `derivedRestrictionMap_comp_derivedBaseChangeMap` with its
  third hypothesis supplied by
  `isZero_higherDirectImage_pushforward_pullbackSquare`. The remaining
  hypotheses are exactly those of the two derived base change maps:
  `R^{q+1} g_*(g^* M) = 0` and `R^{q+1} gZ_*(gZ^* i^* M) = 0`.
- `restrictionCohomologyMap_comp_baseChangeMap_of_vanishing`: the degreewise
  form, from `restrictionCohomologyMap_comp_baseChangeMap`.

## Provenance

The vanishing of higher direct images of flasque sheaves, and the
composite-functor argument `R(g ∘ i')_* = Rg_* ∘ i'_*` and
`R(i ∘ gZ)_* = i_* ∘ RgZ_*` for the exact pushforwards along closed
immersions, are standard facts of sheaf cohomology. Both are derived here
from the Library and Mathlib. No literature statement is formalized, and no
external mathematical assertion is used.

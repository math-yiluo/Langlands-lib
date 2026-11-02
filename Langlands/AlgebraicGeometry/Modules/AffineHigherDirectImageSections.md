# Sections of finitely supported higher direct images over an affine open

This module computes the sections over an affine open of the higher direct
images `R^n f_* M` of a morphism `f : X ⟶ Y`, when all of them have finite
closed support: they are the cohomology of the pullback of `M` to any fibre
product of `f` with `Spec Γ(Y, V) ⟶ Y`, or the homology of any complex
representing its derived sections. All declarations live in the namespace
`Langlands.AlgebraicGeometry.Modules.DerivedSections`.

## Statements

- `affineSections hV N`: for an affine open `V` of a scheme `Y`
  (`hV : IsAffineOpen V`) and `N : Y.Modules`, the sections of `N` over `V`
  as a `Γ(Y, V)`-module. It is defined as the published relative global
  sections `relativeGlobalSections hV.isoSpec.hom` applied to the
  restriction `(Scheme.Modules.restrictFunctor V.ι).obj N`, where
  `hV.isoSpec : V ≅ Spec Γ(Y, V)`.
- `nonempty_relativeCohomology_iso_of_isPullback h₁ h₂ M n`: for
  `f : X ⟶ Y`, `t : Spec R ⟶ Y`, and two pullback squares `h₁` (with
  `q₁ : P₁ ⟶ X`, `f₁ : P₁ ⟶ Spec R`) and `h₂` (with `q₂`, `f₂`) of `f`
  along `t`, there is an isomorphism of `R`-modules between
  `(relativeCohomology f₁ n).obj (q₁^* M)` and
  `(relativeCohomology f₂ n).obj (q₂^* M)`.
- `hasFiniteClosedSupport_restrict hN`: if `N : Y.Modules` has finite
  closed support, so does its restriction to an open `V`.
- `hasFiniteClosedSupport_higherDirectImage_morphismRestrict f M hsupp q`:
  if `(higherDirectImage f q).obj M` has finite closed support for every
  `q`, then so does `(higherDirectImage (f ∣_ V) q).obj` of the restriction
  of `M` to `f ⁻¹ᵁ V`, for every open `V` and every `q`.
- `nonempty_affineSections_higherDirectImage_iso f M hV hsupp h n`: assume
  `(higherDirectImage f q).obj M` has finite closed support for every `q`.
  Let `V` be an affine open of `Y` and `h : IsPullback q f' f hV.fromSpec` a
  pullback square with `q : P ⟶ X` and `f' : P ⟶ Spec Γ(Y, V)`. Then there
  is an isomorphism of `Γ(Y, V)`-modules
  `affineSections hV ((higherDirectImage f n).obj M) ≅
  (relativeCohomology f' n).obj (q^* M)`.
- `nonempty_affineSections_higherDirectImage_iso_homology f M hV hsupp h Kc e n`:
  under the same hypotheses, for every cochain complex `Kc` of
  `Γ(Y, V)`-modules with an isomorphism `e` in the derived category between
  `DerivedCategory.Q.obj Kc` and the image under `DerivedCategory.Plus.ι`
  of the published derived complex of `relativeGlobalSections f'` at
  `q^* M`, there is an isomorphism
  `affineSections hV ((higherDirectImage f n).obj M) ≅ Kc.homology n`.

## Implemented proof

`nonempty_relativeCohomology_iso_of_isPullback`: the comparison
isomorphism `E : P₂ ≅ P₁` of the two pullbacks (`IsPullback.isoIsPullback`)
satisfies `E.hom ≫ q₁ = q₂` and `E.hom ≫ f₁ = f₂`. After substituting, the
published `relativeCohomologyPullbackIso E f₁` identifies the cohomology
along `f₁` with that along `E.hom ≫ f₁` of the `E.hom`-pullback, and
`Scheme.Modules.pullbackComp E.hom q₁` identifies that pullback with
`(E.hom ≫ q₁)^* M`.

`hasFiniteClosedSupport_restrict`: by the published
`mem_stalkSupport_restrict_iff`, the stalk support of the restriction is
the preimage under the open embedding `V.ι` of the stalk support of `N`;
finiteness follows by injectivity, and each singleton `{x}` is the preimage
of the closed singleton `{V.ι x}`.

`hasFiniteClosedSupport_higherDirectImage_morphismRestrict`: transport the
previous lemma along the published `higherDirectImageRestrictIso f V M q`,
which identifies `R^q (f ∣_ V)_*` of the restriction with the restriction of
`R^q f_* M`, using `hasFiniteClosedSupport_iff_of_iso`.

`nonempty_affineSections_higherDirectImage_iso`: compose
1. the inverse of `relativeGlobalSections hV.isoSpec.hom` applied to
   `higherDirectImageRestrictIso f V M n`;
2. the inverse of the published Leray isomorphism `finiteClosedSupportLeray`
   for `f ∣_ V` followed by `hV.isoSpec.hom`, which applies by the previous
   lemma; it identifies the global sections of `R^n (f ∣_ V)_*` with the
   relative cohomology along the published `affineRestrict f hV`;
3. the relative cohomology along `affineRestrict f hV` applied to
   `Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ V).ι`, which replaces
   restriction by pullback;
4. the first lemma, applied to the published pullback square
   `isPullback_affineRestrict f hV` and `h`.

`nonempty_affineSections_higherDirectImage_iso_homology`: compose the
previous isomorphism with the inverse of the published
`Cohomology.DerivedPlus.homologyIsoOfIsoDerivedComplex _ e n`, which
identifies the relative cohomology with `Kc.homology n`. The derived
category is the standard one (`HasDerivedCategory.standard`, a local
instance).

## Provenance and scope

These are internal helpers for the direct-image half of Edixhoven, van
der Geer and Moonen, *Abelian Varieties* (registered source
`edixhoven-vandergeer-moonen-abelian-varieties-draft`), Theorem (9.1),
steps (9.6)–(9.9) of its proof: with
`f` the projection `A × D → D` and `M` the Poincaré bundle, the sections of
`R^n p_* P` over an affine open of the dual are the homology of a perfect
complex computing the cohomology of the Poincaré bundle over that open.
The finite-support hypothesis is what makes the Leray comparison
available; the theorems say nothing without it.

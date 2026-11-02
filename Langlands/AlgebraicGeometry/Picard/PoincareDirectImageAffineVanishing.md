# Cohomology of the Poincaré bundle over affine schemes avoiding the origin

This module is a helper for the direct-image half of
`AlgClosedFieldPoincareDirectImageStatement` (Edixhoven, van der Geer and
Moonen, *Abelian Varieties*, registered source
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, Theorem (9.1)). It
shows that the cohomology of the
Poincaré bundle over any affine scheme mapping to the dual away from the
origin vanishes, and turns this into the acyclicity, after inverting a
function vanishing at the origin, of a complex of modules computing the
cohomology of the Poincaré bundle over an affine open of the dual. All
declarations live in the namespace `Langlands.AbelianScheme`.

## Statements

As in `PoincareDirectImageSupport`, `K` is an algebraically closed field,
`A` an abelian scheme over `Spec K`, `hA : HasDualScheme A`,
`D := dualScheme A hA`, `p := ((baseChange D.hom).obj A).X.hom` the
Poincaré projection `A ×_K D → D`, `P := (poincareLineBundle A hA).obj`, and
`o := (dualOrigin A hA).left (IsLocalRing.closedPoint K)` the point of `D`
at the origin. The theorems about the Poincaré bundle assume the instance
`LocallyOfFiniteType D.hom`.

- `poincare_isZero_relativeCohomology_of_isPullback K A hA y hy h s n`: let
  `y : Spec T ⟶ D.left` be a morphism from an affine scheme with `y t ≠ o`
  for every point `t`, and let `h : IsPullback a b p y` exhibit `Z` (with
  `a : Z ⟶ A ×_K D`, `b : Z ⟶ Spec T`) as a fibre product of `p` and `y`.
  Then for every morphism `s : Z ⟶ Spec R` and every `n : ℕ`,
  `(relativeCohomology s n).obj (a^* P)` is zero.
- `poincare_isZero_homology_baseChange_of_avoids_origin K A hA hV φ hφ Kc e n`:
  let `V` be an affine open of `D`, `φ : Γ(D, V) ⟶ T` a ring map with
  `(Spec.map φ ≫ hV.fromSpec) t ≠ o` for every point `t` of `Spec T`, and `Kc`
  a cochain complex of `Γ(D, V)`-modules. Write `W` for the pullback of `p`
  along `hV.fromSpec` and `Z` for the pullback of
  `pullback.snd p hV.fromSpec : W ⟶ Spec Γ(D, V)` along `Spec.map φ`. Given
  an isomorphism `e` in the (standard) derived category between the base
  change `(Cohomology.ModuleComplex.baseChange φ.hom).obj Kc` and the
  published derived complex of `relativeGlobalSections (Z ⟶ Spec T)` at the
  pullback to `Z` of the line bundle
  `(LineBundle.pullback (pullback.fst p hV.fromSpec)).obj (poincareLineBundle A hA)`,
  the homology of the base change of `Kc` along `φ` vanishes in every degree
  `n : ℤ`.
- `fromSpec_away_ne_of_mem_primeIdealOf hV hy hf t`: for a scheme `Y`, an
  affine open `V`, a point `y ∈ V`, and `f : Γ(Y, V)` in the prime ideal
  `hV.primeIdealOf ⟨y, hy⟩` of `y`, the composite
  `Spec Γ(Y, V)_f ⟶ Spec Γ(Y, V) ⟶ Y` (the first map induced by
  `algebraMap Γ(Y, V) (Localization.Away f)`) does not take the value `y`
  at any point `t`.
- `poincare_isZero_homology_localization_of_mem_originIdeal K A hA hV hx Kc hbc f hf n`:
  let `V` be an affine open of `D` with `hx : o ∈ V`, and `Kc` a cochain
  complex of `Γ(D, V)`-modules such that for every ring map
  `φ : Γ(D, V) ⟶ T` there is an isomorphism `e` as in the previous theorem
  (hypothesis `hbc`). Then for every `f` in the prime ideal
  `hV.primeIdealOf ⟨o, hx⟩` of the origin and every `n : ℤ`, the homology in
  degree `n` of the base change of `Kc` along
  `algebraMap Γ(D, V) (Localization.Away f)` is zero.

The derived category used in the last two statements is the standard one
(`HasDerivedCategory.standard`, a local instance).

## Implemented proof

`poincare_isZero_relativeCohomology_of_isPullback`. Let `U` be the open
`rationalPointComplement D.hom {dualOrigin A hA} _`, whose points are those
`≠ o`. Since `y` misses `o`, it factors as `x ≫ U.ι` through the open
immersion (`IsOpenImmersion.lift`). The restriction `p ∣_ U` is smooth and
proper (base change of `p` along `U.ι`, by `isPullback_morphismRestrict`).
For the line bundle `Q`, the restriction of the Poincaré bundle to
`p ⁻¹ᵁ U`, every `R^q (p ∣_ U)_* Q` is zero: by the published
`higherDirectImageRestrictIso` and `restrictFunctorIsoPullback` it is the
restriction to `U` of `R^q p_* P`, which is zero by
`poincareDirectImage_isZero_away_from_origin`. The published
`higherDirectImageVanishingAffineBaseChange` then gives vanishing of the
cohomology of `Q` pulled back to the fibre product of `p ∣_ U` with `x`;
`Scheme.Modules.pullbackComp` rewrites it as the pullback of `P` along the
composite to `A ×_K D`. Pasting the chosen pullback square of `p ∣_ U` and
`x` with the square of `isPullback_morphismRestrict` exhibits that fibre
product as a pullback of `p` along `x ≫ U.ι = y`, and the published
`isZero_relativeCohomology_of_isPullback` (with the identity of `Spec T`)
transports the vanishing to `Z`, `a` and any affine base `s`.

`poincare_isZero_homology_baseChange_of_avoids_origin`. In negative degrees
the homology of the base change is the homology of the derived complex
through `e` and `DerivedCategory.homologyFunctorFactors`, and it vanishes
by the published `Cohomology.DerivedPlus.isZero_homology_of_neg`. In a
degree `m ≥ 0`, the published
`Cohomology.DerivedPlus.homologyIsoOfIsoDerivedComplex` identifies the
homology with `relativeCohomology (Z ⟶ Spec T) m` of the pulled-back line
bundle, which `Scheme.Modules.pullbackComp` identifies with the
cohomology of the pullback of `P` along `Z ⟶ W ⟶ A ×_K D`. Pasting the two
chosen pullback squares shows that `Z` is a pullback of `p` along
`Spec.map φ ≫ hV.fromSpec`, so the first theorem applies.

`fromSpec_away_ne_of_mem_primeIdealOf`. If the composite took the value
`y` at `t`, then, since `hV.fromSpec` is injective and sends
`hV.primeIdealOf ⟨y, hy⟩` to `y` (`IsAffineOpen.fromSpec_primeIdealOf`),
the image of `t` in `Spec Γ(Y, V)` would be that prime, so `f` would lie in
its preimage ideal: the image of `f` in `Γ(Y, V)_f` would lie in the prime
`t`. But that image is a unit (`IsLocalization.Away.algebraMap_isUnit`),
which contradicts primality.

`poincare_isZero_homology_localization_of_mem_originIdeal` applies the
second theorem to `φ := CommRingCat.ofHom (algebraMap Γ(D, V)
(Localization.Away f))`, with the avoidance condition from the third
theorem and the isomorphism chosen from `hbc`.

## Provenance and scope

In Edixhoven, van der Geer and Moonen's proof of Theorem (9.1) the complex `K•` computing
`R p_* P` near the origin has cohomology supported at the origin, because
`R^n p_* P` vanishes away from it (the support step). The last theorem is
the form of this fact used in the local algebra at the origin: the complex
becomes acyclic after inverting any function vanishing at the origin. The
route through the published affine-base-change vanishing theorem is
internal to this formalization. Nothing is claimed about the cohomology at
the origin itself.

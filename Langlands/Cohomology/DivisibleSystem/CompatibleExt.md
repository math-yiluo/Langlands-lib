# Levelwise evaluation of Ext groups and derived morphisms of inverse systems

Author: Worker 61. Built on the Library module
`Langlands.Cohomology.DivisibleSystem.TowerComplex` (`towerComplex`); through
it, it uses `DivisibleSystem` (`Langlands.Cohomology.DivisibleSystem`). From
Mathlib it uses the evaluation functors `evaluation ℕᵒᵖ C`, `homOfLE`,
`Functor.mapHomologicalComplex`, `NatTrans.mapHomologicalComplex`,
`Abelian.Ext` with `HasExt`, `Abelian.Ext.mk₀`, `Abelian.Ext.comp`,
`Abelian.Ext.homEquiv₀`, `Abelian.Ext.addEquiv₀`, `Abelian.Ext.mk₀_bijective`,
`Abelian.Ext.mk₀_comp_mk₀`, `Abelian.Ext.mk₀_eq_zero_iff`,
`Functor.mapExtAddHom` and `Abelian.Ext.mapExactFunctor` with the lemmas
`Abelian.Ext.mapExactFunctor_mk₀` and
`Abelian.Ext.mapExactFunctor_comp_mk₀_natTransApp`
(`Mathlib.Algebra.Homology.DerivedCategory.Ext.Map`), and, for derived
categories, `HasDerivedCategory`, `DerivedCategory.Q`,
`Functor.mapDerivedCategory`, `Functor.mapDerivedCategoryFactors`,
`NatTrans.mapDerivedCategory`, `NatTrans.mapDerivedCategory_app_Q_obj`,
`Functor.commShiftIso` and `NatTrans.shift_app_comm`.

## Conventions

`C` is an abelian category (objects in `Type u`, morphisms in `Type v`).
`ℕᵒᵖ ⥤ C` is the abelian category of inverse systems in `C`; for an inverse
system `X` and `m : ℕ`, `X m` is `X.obj (op m)`. Evaluation at `m`,
`(evaluation ℕᵒᵖ C).obj (op m) : (ℕᵒᵖ ⥤ C) ⥤ C`, is additive and preserves
finite limits and colimits (limits and colimits in functor categories are
computed pointwise), so Mathlib's constructions for exact functors apply to it.
For `m' ≤ m`, `(evaluation ℕᵒᵖ C).map (homOfLE h).op` is the natural
transformation from evaluation at `m` to evaluation at `m'` whose component
at `X` is the transition morphism `X m ⟶ X m'`.

The Ext groups are Mathlib's `Abelian.Ext`: in section `Ext` the hypotheses
`HasExt.{w} C` and `HasExt.{w'} (ℕᵒᵖ ⥤ C)` are assumed, so that
`Ext^n(X, Y)` for inverse systems is computed in the category `ℕᵒᵖ ⥤ C` (in
`Type w'`) and `Ext^n(X m, Y m)` in `C` (in `Type w`). In section `Derived`,
`HasDerivedCategory.{t} C` and `HasDerivedCategory.{t'} (ℕᵒᵖ ⥤ C)` are
assumed and `Q` is the localization functor from cochain complexes to the
derived category. These instances are hypotheses; none is constructed.

The names `systemTransition`, `evalComplex` and `evalComplexTransition` are
distinct from the published `levelMap` and `levelComplex` of
`Langlands.Cohomology.DivisibleSystem.Resolution` (in the same namespace),
which are different constructions: there a complex indexed by `ℕ` is
assembled at a level from a sequence of `ℓ`-divisible systems. This module can
be imported together with every Library module that mentions
`DivisibleSystem`.

## Ext groups (namespace `Langlands.Cohomology.DivisibleSystem`)

Here `X Y : ℕᵒᵖ ⥤ C` and `n : ℕ`.

- `systemTransition X h` (`abbrev`): for `h : m' ≤ m`, the transition morphism
  `X.map (homOfLE h).op : X m ⟶ X m'`.
- `extEval X Y n m`: the additive map `Ext^n(X, Y) →+ Ext^n(X m, Y m)`,
  Mathlib's `Functor.mapExtAddHom` for evaluation at `m`; `extEval_apply`
  records that it is `Abelian.Ext.mapExactFunctor`.
- `extEval_mk₀ X Y m f`: in degree `0` it maps `Ext.mk₀ f` to
  `Ext.mk₀ (f.app (op m))` (Mathlib's `mapExactFunctor_mk₀`).
- `extEval_comp_mk₀ X Y α h`: for `h : m' ≤ m`, composing
  `extEval X Y n m α` with `Ext.mk₀ (systemTransition Y h)` gives the same class in
  `Ext^n(X m, Y m')` as composing `Ext.mk₀ (systemTransition X h)` with
  `extEval X Y n m' α`. This is Mathlib's
  `mapExactFunctor_comp_mk₀_natTransApp` for the natural transformation from
  evaluation at `m` to evaluation at `m'`.
- `compatibleExt X Y n`: the additive subgroup of the product
  `∏_m Ext^n(X m, Y m)` of the families `e` with
  `(e m).comp (Ext.mk₀ (systemTransition Y h)) = (Ext.mk₀ (systemTransition X h)).comp (e m')`
  in `Ext^n(X m, Y m')` for all `m' ≤ m`; `mem_compatibleExt_iff` unfolds the
  membership. Closure under addition, zero and negation follows from the
  bilinearity of `Ext.comp`. Because Ext is contravariant in the first and
  covariant in the second variable, this is the equalizer of the two maps from
  `∏_m Ext^n(X m, Y m)` to `∏_{m' ≤ m} Ext^n(X m, Y m')`, not an inverse limit
  along transition maps between the groups `Ext^n(X m, Y m)`.
- `extToCompatible X Y n`: the additive map from `Ext^n(X, Y)` to
  `compatibleExt X Y n` sending `α` to the family `m ↦ extEval X Y n m α`,
  which is compatible by `extEval_comp_mk₀`; `extToCompatible_apply_coe`
  gives its components.
- `extToCompatible_bijective_zero X Y`: in degree `0` this map is bijective.
  Injectivity: write the class as `Ext.mk₀ f` for a morphism of inverse
  systems `f` (`mk₀_bijective`); if all its levelwise images
  `Ext.mk₀ (f.app (op m))` vanish then every component `f.app (op m)` is zero
  (`mk₀_eq_zero_iff`), so `f = 0`. Surjectivity: for a compatible family `e`,
  the morphisms `homEquiv₀ (e m)` are natural in `m`, by the compatibility
  condition, `mk₀_comp_mk₀` and the injectivity of `mk₀`, so they form a
  morphism `f : X ⟶ Y` with `extToCompatible X Y 0 (Ext.mk₀ f) = e`.
- `compatibleExtZeroAddEquiv X Y`: the resulting additive equivalence between
  morphisms `X ⟶ Y` of inverse systems and `compatibleExt X Y 0`, Mathlib's
  `Ext.addEquiv₀` inverted followed by `extToCompatible X Y 0`.

In positive degrees `extToCompatible` is not claimed to be injective or
surjective, and nothing about its kernel or image is proved.

## Level complexes (namespace `Langlands.Cohomology.DivisibleSystem`)

Here `K : CochainComplex (ℕᵒᵖ ⥤ C) ℤ`.

- `evalComplex K m` (`abbrev`): the cochain complex in `C` obtained by
  applying evaluation at `m` termwise (`Functor.mapHomologicalComplex`).
- `evalComplexTransition K h` (`abbrev`): for `h : m' ≤ m`, the chain map
  `evalComplex K m ⟶ evalComplex K m'` given termwise by the transition
  morphisms (`NatTrans.mapHomologicalComplex`).
- `evalComplex_towerComplex T m`: for an `ℓ`-divisible system `T` of cochain
  complexes in `C`, the level `m` complex of the published
  `towerComplex T` is `T m`, by definition (`rfl`).

## Derived morphisms (namespace `Langlands.Cohomology.DivisibleSystem`)

Here `K L : CochainComplex (ℕᵒᵖ ⥤ C) ℤ` and `n : ℤ`.

- `derivedEval K L n m`: the additive map from morphisms
  `Q.obj K ⟶ (Q.obj L)⟦n⟧` in the derived category of inverse systems to
  morphisms `Q.obj (evalComplex K m) ⟶ (Q.obj (evalComplex L m))⟦n⟧` in the
  derived category of `C`. It applies Mathlib's `mapDerivedCategory` of
  evaluation at `m`, then its shift isomorphism `commShiftIso n` at `Q.obj L`,
  and composes on both sides with the isomorphisms `mapDerivedCategoryFactors`
  identifying the image of `Q.obj K` with `Q.obj (evalComplex K m)` (and
  likewise for `L`, shifted by `n`).
- `derivedEval_comp K L n f h`: for `h : m' ≤ m`,
  `derivedEval K L n m f ≫ (Q.map (evalComplexTransition L h))⟦n⟧'` equals
  `Q.map (evalComplexTransition K h) ≫ derivedEval K L n m' f`. The proof uses the
  natural transformation `NatTrans.mapDerivedCategory τ` induced by the
  transition `τ` from evaluation at `m` to evaluation at `m'`: its naturality
  at `f`, its compatibility with the shift (`NatTrans.shift_app_comm`), and its
  value on `Q.obj K` and `Q.obj L` (`NatTrans.mapDerivedCategory_app_Q_obj`),
  which is `Q.map` of the level chain map up to the isomorphisms
  `mapDerivedCategoryFactors`.
- `compatibleDerived K L n`: the additive subgroup of the families
  `e m : Q.obj (evalComplex K m) ⟶ (Q.obj (evalComplex L m))⟦n⟧` with
  `e m ≫ (Q.map (evalComplexTransition L h))⟦n⟧' = Q.map (evalComplexTransition K h) ≫ e m'`
  for all `m' ≤ m`; `mem_compatibleDerived_iff` unfolds the membership.
- `derivedToCompatible K L n`: the additive map
  `f ↦ (m ↦ derivedEval K L n m f)` into `compatibleDerived K L n`;
  `derivedToCompatible_apply_coe` gives its components. It is not claimed to
  be injective or surjective.
- `towerDerivedEval T W n m`: for `ℓ`-divisible systems `T` and `W` of cochain
  complexes in `C`, `derivedEval` for `towerComplex T` and `towerComplex W`,
  with target the morphisms `Q.obj (T m) ⟶ (Q.obj (W m))⟦n⟧`.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), end of the proof of Proposition 4.10,
printed p.312 (one-based PDF page 14; Worker 61 read the rendered scanned
page). There Harris works at the finite levels `m` with the groups
"`T_m(j, ẽ) = Hom_{𝒪/ℓ^m 𝒪[S(ẽ)]}(C^j_m(ẽ)^{H_p}, Hom(𝒪_m[C_p/H_p]^M, 𝓛_m))`",
shows that the maps "(4.10.3) `T_{m+1}(j, ẽ) → T_m(j, ẽ)`" are surjective and,
using the finiteness of the right-hand side of the spectral sequence (4.9),
that "the complexes in (4.10.2) satisfy a Mittag-Leffler condition", and
concludes "the stronger (integral) statement (4.10.4)
`E_2^{i,j} = Ext^i(H_c^{2(n-1)-j}(M̆_N, 𝒪(n-1)), 𝒜_ℓ(GJ, 𝓛, H)) ⇒
H^{i+j}(S̄_{K(N)}, 𝓛̃)`".

This module provides, in our own formulation, the canonical maps from Ext
groups and derived morphisms of inverse systems to compatible families of
their finite-level counterparts, with the degree `0` identification. They are
the comparison one needs to relate integral Ext groups, read as Ext groups in
the category of inverse systems as in the Library module
`Langlands.Cohomology.DivisibleSystem.AdicHyperext` (our interpretation;
Harris does not say in which category his integral Ext groups are taken), to
the levelwise groups. Harris's finite-level groups are taken over the
coefficients `𝒪/ℓ^m 𝒪`, which vary with `m`; here all levels lie in the fixed
category `C`, and no change of coefficients is formalized. No Mittag-Leffler
argument and no bijectivity in positive degrees is proved.

The constructions, statements and proofs are ours; the module is derived.

## Scope

The module does not construct Harris's complexes (4.10.2) or the groups
`T_m(j, ẽ)`, does not prove the Mittag-Leffler condition or any `lim¹`
vanishing, and does not prove that `extToCompatible` or
`derivedToCompatible` is injective or surjective in positive degrees. The
existence of Ext groups and derived categories for `C` and `ℕᵒᵖ ⥤ C` is
assumed, not proved.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.

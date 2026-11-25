/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Open.OpenImmersionSquare
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.WeaklyEtale
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekBaseChangeMate

/-!
# Sections of the fixed-scalar open-square mate

Source: Stacks Project, Tag 03CF, lemma-localize-morphism; the published pro-etale
inverse-image compositors and restriction comparisons
(blueprint: lem-sf-fixed-scalar-open-square-section-mate).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.ProEtale

/-- The specified inverse-image square mate, transported to literal open restrictions.
The inverse-image compositor is `upperStarCompIso`; both restriction isomorphisms are
normalized by uniqueness of left adjoints with the common pushforward right adjoint.
Source: Stacks Project, Tag 03CF, lemma-localize-morphism, with the published pro-etale
mate normalization (blueprint: lem-sf-fixed-scalar-open-square-section-mate). -/
def fixedScalarOpenSquareRestrictionMate
    (A : Type (u + 1)) [CommRing A]
    {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] [IsOpenImmersion j']
    (w : gU ≫ j = j' ≫ g) :
    lowerStar (ModuleCat.{u + 1} A) g ⋙
        openImmersionRestriction (ModuleCat.{u + 1} A) j ⟶
      openImmersionRestriction (ModuleCat.{u + 1} A) j' ⋙
        lowerStar (ModuleCat.{u + 1} A) gU :=
  Functor.whiskerLeft (lowerStar (ModuleCat.{u + 1} A) g)
      (upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j).inv ≫
    (mateEquiv (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g)
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) gU)
      (upperStarCompIso (ModuleCat.{u + 1} A) w).hom) ≫
    Functor.whiskerRight (upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j').hom
      (lowerStar (ModuleCat.{u + 1} A) gU)

/-- The section map `c_W : W ×_U U' ⟶ W ×_X X'`, as a morphism over `X'`.
Its underlying scheme arrow is the pullback lift of `pr_W` and `pr_U' ≫ j'`.
Source: Stacks Project, Tag 03CF, lemma-localize-morphism; the explicit fiber-product
comparison (blueprint: lem-sf-fixed-scalar-open-square-section-mate). -/
def fixedScalarOpenSquareSectionComparison
    {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) [IsOpenImmersion j] [IsOpenImmersion j']
    (w : gU ≫ j = j' ≫ g) :
    MorphismProperty.Over.pullback @WeaklyEtale ⊤ gU ⋙
        MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j') ⟶
      MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j) ⋙
        MorphismProperty.Over.pullback @WeaklyEtale ⊤ g :=
  MorphismProperty.Over.pullbackMapComparison
    (inferInstance : WeaklyEtale j) (inferInstance : WeaklyEtale j') ⟨w⟩

/-- The transported mate evaluates to `N(c_W)`, an equality in `ModuleCat A`.
Both sides are natural in `W` and `N`: the left side is a natural transformation of
sheaf functors and the right side applies a presheaf to a natural site comparison.
Source: Stacks Project, Tag 03CF, lemma-localize-morphism; explicit normalization of
the published pro-etale square (blueprint: lem-sf-fixed-scalar-open-square-section-mate).

Proof (the delivered route, node `lem-sf-fixed-scalar-open-square-section-mate`):
1. `baseChangeMap_eq_mateEquiv` (at the coefficient category `ModuleCat A` and the commutative
   square underlying the open square) identifies the mate of `upperStarCompIso` along
   `g^* ⊣ g_*` and `gU^* ⊣ gU_*` with `baseChangeMap`; it applies
   `iterated_mateEquiv_conjugateEquiv` (`lem-trf-iterated-square-mates`) and the conjugate of
   `upperStarCompIso` computed from the compositors (`proposition-topos-functoriality--3`,
   `proposition-topos-functoriality--3`, `def-weil-pbc-adjunction-conjugate`).
2. `baseChangeMap_eq` rewrites `baseChangeMap` as `localizationRestrictionBaseChangeMap`
   conjugated by `upperStarIsoLocalizationRestriction` at `j` and its inverse at `j'`; it is
   proved by `mateEquiv_leftAdjointUniq` and `mateEquiv_localizationRestrictionBaseChangeMap`
   (`lem-weil-pbc-adjoint-continuous-restriction-adjunction`,
   `situation-conventions`, `lem-weil-pbc-mate-pasting`).
3. `upperStarIsoOpenImmersionRestriction` is `upperStarIsoLocalizationRestriction`, so the
   outer comparisons of the transported mate cancel the inner ones: the transported mate is
   `localizationRestrictionBaseChangeMap`.
4. That map is `sheafPushforwardContinuousNatTrans` of `pullbackMapComparison`, which is
   `fixedScalarOpenSquareSectionComparison`; pushforward evaluates by precomposition
   (`proposition-topos-functoriality--2`), so the component at `N` and `W` is `N(c_W)` by `rfl`.
   Naturality in `W` and `N` is part of these natural transformations. -/
theorem fixed_scalar_open_square_section_mate
    (A : Type (u + 1)) [CommRing A]
    {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) (sq : OpenImmersionSquare gU j' j g)
    (N : Sheaf (Scheme.ProEt.topology X') (ModuleCat.{u + 1} A)) (W : U.ProEt) :
    ((@fixedScalarOpenSquareRestrictionMate.{u} A _ U' U X' X gU j' j g
      sq.isOpenImmersion sq.isOpenImmersion' sq.toCommSq.w).app N).hom.app (op W) =
      N.obj.map ((@fixedScalarOpenSquareSectionComparison.{u} U' U X' X gU j' j g
        sq.isOpenImmersion sq.isOpenImmersion' sq.toCommSq.w).app W).op := by
  let := sq.isOpenImmersion
  let := sq.isOpenImmersion'
  have h : fixedScalarOpenSquareRestrictionMate A gU j' j g sq.toCommSq.w =
      localizationRestrictionBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq := by
    unfold fixedScalarOpenSquareRestrictionMate
    rw [← baseChangeMap_eq_mateEquiv (ModuleCat.{u + 1} A) sq.toCommSq,
      baseChangeMap_eq (ModuleCat.{u + 1} A) sq.toCommSq]
    apply NatTrans.ext
    funext M
    simp [upperStarIsoOpenImmersionRestriction, Category.assoc, ← Functor.map_comp]
  rw [h]
  rfl

end AlgebraicGeometry.ProEtale

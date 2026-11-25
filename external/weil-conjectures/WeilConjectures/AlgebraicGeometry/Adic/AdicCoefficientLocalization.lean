/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.InternalHomEvaluation

/-! # The actual adic coefficient map under localization -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace AlgebraicGeometry.ProEtale

/-- The actual coefficient pullback is the identity on functions after localization.
Source: Stacks 03CE and the native coefficient pullback adjunction.
(blueprint: lem-sf-adic-coefficient-localization).
The two inverse-image functors are left adjoints to the same direct image. Apply the
localization adjunction to their comparison followed by the identity on coefficient
functions. Its adjunct is precomposition with the pullback projection, which is the
native coefficient map to direct image. Adjunction injectivity identifies the maps. -/
theorem comparisonNativeCoefficient {l : ℕ} [Fact l.Prime]
    {V W : Scheme.{u}} (g : W ⟶ V) (hg : WeaklyEtale g) :
    upperStarAdicConstantSheafHom l g =
      (upperStarIsoLocalizationRestriction (WeilCoefficients.{u} l) g hg).hom.app
        (adicConstantSheaf l V) ≫
          (adicConstantSheafLocalizationRestrictionIso l g hg).hom := by
  let adj1 := upperStarLowerStarAdjunction (WeilCoefficients.{u} l) g
  let adj2 := localizationRestrictionLowerStarAdjunction (WeilCoefficients.{u} l) g hg
  apply (adj1.homEquiv _ _).injective
  change adj1.homEquiv _ _ ((adj1.homEquiv _ _).symm
    (adicConstantSheafToLowerStar l g)) = _
  rw [Equiv.apply_symm_apply, adj1.homEquiv_naturality_right]
  erw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
  apply Sheaf.hom_ext
  ext U s
  rw [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ConcreteCategory.comp_apply]
  erw [localizationRestrictionLowerStarAdjunction_unit_app_hom_app]
  rfl

end AlgebraicGeometry.ProEtale

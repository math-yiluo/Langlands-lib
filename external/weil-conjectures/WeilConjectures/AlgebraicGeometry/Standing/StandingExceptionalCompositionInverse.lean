/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Standing.StandingExceptionalComposition

/-! # Explicit inverse candidate for the standing exceptional compositor

The inverse compact-support compositor is transposed in the reverse direction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale

/-- The explicit inverse candidate: apply the inverse f and g Hom bijections to the
identity at f!g!L, precompose with alpha inverse, then transpose through gf.
Source: the inverse-transpose argument in the exceptional-composition clause of
proposition-compatibility-purity-composition--1; no inverse is chosen from an existence theorem.
(blueprint: def-pur-standing-composition-inverse). -/
def standingExceptionalCompositionInverse (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y S : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [S.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (S ↘ Spec (.of P.field.k))]
    [QuasiCompact (S ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) (g : Y ⟶ S)
    [f.IsOver (Spec (.of P.field.k))] [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g] :=
  letI : Finite P.Ring := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos
  letI : Finite P.Coefficient := inferInstanceAs (Finite (ULift.{u + 1} P.Ring))
  letI : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ Spec (.of P.field.k))
  letI : IsLocallyNoetherian S :=
    LocallyOfFiniteType.isLocallyNoetherian (S ↘ Spec (.of P.field.k))
  letI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace
    (Y ↘ Spec (.of P.field.k))
  letI : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace
    (S ↘ Spec (.of P.field.k))
  let A := ModuleCat.{u + 1} P.Coefficient
  fun (L : DerivedCategoryBoundedConstructible A S) ↦
    let hL := L.property.plusEtaleOrigin.plus
    let V := (rightDerivedUpperShriek P.Coefficient f).obj
      ((rightDerivedUpperShriek P.Coefficient g).obj L.obj)
    let hV := plusEtaleOrigin_rightDerivedUpperShriek_obj f
      (plus_rightDerivedUpperShriek_obj g hL)
    let hg := standingExceptionalHomEquiv P.Coefficient g
      (hV.rightDerivedLowerShriek_obj f) hL
    let hf := standingExceptionalHomEquiv P.Coefficient f hV
      (plus_rightDerivedUpperShriek_obj g hL)
    let alpha := (originCompositionAmbient P.Coefficient f g).inv.app ⟨V, hV⟩
    standingExceptionalHomEquiv P.Coefficient (f ≫ g) hV hL
      (alpha ≫ hg.symm (hf.symm (𝟙 V)))

end AlgebraicGeometry.ProEtale

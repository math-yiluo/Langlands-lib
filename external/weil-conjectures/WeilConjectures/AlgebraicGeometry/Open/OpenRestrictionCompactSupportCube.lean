/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Open.OpenRestrictionCompactSupport
import WeilConjectures.AlgebraicGeometry.Open.OpenSupportBaseChangedCube
import WeilConjectures.AlgebraicGeometry.Open.OpenSupportCompactificationNaturality

/-! # The compact-support cube for restriction to an open
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

attribute [local irreducible] openRestrictionGraphIso sfGraphCompactificationComparison
  openSupportCompactificationIso rightDerivedLowerShriekOfCompactificationIso
  rightDerivedLowerShriekOfCompactificationBaseChangeMap
  derivedOpenImmersionLowerShriekBaseChangeIso

/-- The two compact-support pastings on an open-restriction cube agree. -/
theorem openRestrictionCompactSupport_cube
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y X' Y' U V U' V' : Scheme.{u}}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
    [HasCompactification f] [HasCompactification f'] [QuasiCompact f']
    (sq : IsPullback g' f' f g)
    {j : U ⟶ Y} [IsOpenImmersion j] {a : V ⟶ X} [IsOpenImmersion a]
    {p : V ⟶ U} (sqU : IsPullback a p f j) [HasCompactification p]
    {c : U' ⟶ U} {j' : U' ⟶ Y'} [IsOpenImmersion j']
    (sqj : IsPullback c j' j g)
    {b : V' ⟶ V} {p' : V' ⟶ U'} (sq' : IsPullback b p' p c)
    [HasCompactification p'] [QuasiCompact p']
    {a' : V' ⟶ X'} [IsOpenImmersion a'] (sqV : IsPullback a' p' f' j')
    (sqA : IsPullback b a' a g') :
    letI := isIso_rightDerivedLowerShriekBaseChangeMap Λ sq
    letI := isIso_rightDerivedLowerShriekBaseChangeMap Λ sq'
    (TwoSquare.vComp
      (TwoSquare.mk _ _ _ _ (inv (rightDerivedLowerShriekBaseChangeMap Λ sq')))
      (TwoSquare.mk _ _ _ _
        (derivedOpenImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} Λ) sqj).hom)
      ).whiskerLeft (openRestrictionCompactSupportIso Λ sqU).hom =
    (TwoSquare.vComp
      (TwoSquare.mk _ _ _ _
        (derivedOpenImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} Λ) sqA).hom)
      (TwoSquare.mk _ _ _ _ (inv (rightDerivedLowerShriekBaseChangeMap Λ sq)))
      ).whiskerRight (openRestrictionCompactSupportIso Λ sqV).hom := by
  let A := ModuleCat.{u + 1} Λ
  let cf := HasCompactification.compactification f
  let cp := HasCompactification.compactification p
  let df := HasCompactification.compactification f'
  let dp := HasCompactification.compactification p'
  let ef := compactificationSupportBaseChangeIso Λ sq cf
  let ep := compactificationSupportBaseChangeIso Λ sq' cp
  let If := rightDerivedLowerShriekOfCompactificationIso Λ (cf.ofIsPullback sq) df
  let Ip := rightDerivedLowerShriekOfCompactificationIso Λ (cp.ofIsPullback sq') dp
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ sq
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ sq'
  have hEU : openRestrictionCompactSupportIso Λ sqU =
      openSupportCompactificationIso Λ sqU cf cp := by
    unfold openRestrictionCompactSupportIso openSupportCompactificationIso
    rfl
  have hEV : openRestrictionCompactSupportIso Λ sqV =
      openSupportCompactificationIso Λ sqV df dp := by
    unfold openRestrictionCompactSupportIso openSupportCompactificationIso
    rfl
  ext K
  have h := NatTrans.congr_app
    (openSupportBaseChanged_cube Λ sq sqU sqj sq' sqV sqA cf cp) K
  have hn := NatTrans.congr_app
    (openSupportCompactificationIso_naturality Λ sqV
      (cf.ofIsPullback sq) df (cp.ofIsPullback sq') dp)
        (L((b)^*[A]).obj K)
  have hIf : Rf_!(cf.ofIsPullback sq)[A].map
        ((derivedOpenImmersionLowerShriekBaseChangeIso A sqA).hom.app K) ≫
      If.hom.app _ = If.hom.app _ ≫ Rf_!(df)[A].map
        ((derivedOpenImmersionLowerShriekBaseChangeIso A sqA).hom.app K) :=
    If.hom.naturality _
  simp only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight, TwoSquare.vComp,
    TwoSquare.mk, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id, Category.assoc] at h hn ⊢
  have hefi : inv (rightDerivedLowerShriekBaseChangeMap Λ sq) =
      Functor.whiskerLeft _ If.inv ≫ ef.inv := by
    change inv (ef.hom ≫ Functor.whiskerLeft _ If.hom) = _
    simp only [IsIso.inv_comp, Functor.inv_whiskerLeft, IsIso.Iso.inv_hom]
  have hepi : inv (rightDerivedLowerShriekBaseChangeMap Λ sq') =
      Functor.whiskerLeft _ Ip.inv ≫ ep.inv := by
    change inv (ep.hom ≫ Functor.whiskerLeft _ Ip.hom) = _
    simp only [IsIso.inv_comp, Functor.inv_whiskerLeft, IsIso.Iso.inv_hom]
  rw [hefi, hepi, hEU, hEV]
  dsimp only [rightDerivedLowerShriek, cf, cp, df, dp, A, ef, ep, If, Ip] at h hn hIf ⊢
  dsimp only [Functor.comp_obj] at hIf
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.map_comp, Category.assoc]
  apply (cancel_epi (D((j')_!open[A]).map (Ip.hom.app (L((b)^*[A]).obj K)))).mp
  dsimp only [rightDerivedLowerShriek, cf, cp, df, dp, A, ef, ep, If, Ip]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app_assoc]
  rw [h]
  rw [reassoc_of% hn]
  conv_rhs =>
    arg 2
    rw [← Category.assoc, ← hIf]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]

end AlgebraicGeometry.Etale

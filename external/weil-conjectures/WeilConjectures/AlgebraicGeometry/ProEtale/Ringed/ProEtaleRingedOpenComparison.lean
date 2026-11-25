/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch

import all WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.AlgebraicGeometry.OpenImmersion
import all Mathlib.CategoryTheory.Sites.Over
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all Mathlib.CategoryTheory.Sites.CoverLifting
import all WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement

/-! Ringed pro-etale localization: a geometric step of the open-closed argument.

## References

* Stacks Project, Tags 09BN and 00XZ
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Localization at an open object identifies actual inverse image for an arbitrary
ring-sheaf coefficient with restriction of module sheaves to the slice. There is no
closed-complement or quasi-compactness hypothesis in this comparison. -/
theorem proEtale_ringed_open_comparison {X : Scheme.{u}} (U : X.ProEt)
    [IsOpenImmersion U.hom] (A : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    ∃ q : SheafOfModules.{u + 1}
        ((sheafCompose (ProEt.topology U.left)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          ((proEtaleSheafInverseImage U.hom CommRingCat.{u + 1}).obj A)) ≌
          SheafOfModules.{u + 1} (((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A).over U),
      Nonempty (proEtaleModuleInverseImage U.hom A ⋙ q.functor ≅
        SheafOfModules.overFunctor.{u + 1} ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A) U) := by
  let R := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A
  let S := (sheafCompose (ProEt.topology U.left)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      ((proEtaleSheafInverseImage U.hom CommRingCat.{u + 1}).obj A)
  let G : U.left.ProEt ⥤ X.ProEt := MorphismProperty.Over.map ⊤ U.prop
  let : G.IsContinuous (ProEt.topology U.left) (ProEt.topology X) :=
    ProEt.isContinuous_overMap U.prop
  let : (MorphismProperty.Over.pullback @WeaklyEtale ⊤ U.hom).IsContinuous
      (ProEt.topology X) (ProEt.topology U.left) := ProEt.isContinuous_overPullback U.hom
  let a := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ U.hom U.prop trivial
  let b := a.sheafPushforwardContinuous (E := CommRingCat.{u + 1})
    (ProEt.topology U.left) (ProEt.topology X)
  let c₀ := ((proEtaleSheafAdjunction U.hom CommRingCat.{u + 1}).leftAdjointUniq b).app A
  let c : S ≅ (G.sheafPushforwardContinuous RingCat.{u + 1}
      (ProEt.topology U.left) (ProEt.topology X)).obj R :=
    (sheafCompose (ProEt.topology U.left)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso c₀
  have := ProEt.sliceDense X U
  obtain ⟨q, hq⟩ := ProEt.module_transport ((ProEt.topology X).over U)
    (ProEt.topology U.left) (ProEt.sliceEquiv X U) (R.over U) S c
  let ψ : R ⟶ ((proEtaleBaseChange U.hom).sheafPushforwardContinuous
      RingCat.{u + 1} (ProEt.topology X) (ProEt.topology U.left)).obj S :=
    ⟨Functor.whiskerRight
      ((proEtaleSheafAdjunction U.hom CommRingCat.{u + 1}).unit.app A).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  have H₁ : Functor.whiskerRight (NatTrans.op a.counit) R.obj =
      ψ.hom ≫ (proEtaleBaseChange U.hom).op.whiskerLeft c.hom.hom := by
    apply NatTrans.ext
    funext V
    have hc := Adjunction.unit_leftAdjointUniq_hom_app
      (proEtaleSheafAdjunction U.hom CommRingCat.{u + 1}) b A
    exact congrArg (fun f ↦ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
      (f.hom.app V)) hc.symm
  have H₂ : c.hom.hom ≫ G.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op a.unit) S.obj = 𝟙 S.obj := by
    apply NatTrans.ext
    funext V
    apply (cancel_mono (c.hom.hom.app V)).mp
    dsimp
    rw [Category.id_comp]
    have hn := c.hom.hom.naturality (a.unit.app V.unop).op
    dsimp at hn
    rw [Category.assoc, Category.assoc, hn]
    have hh := congrArg (fun t ↦ t.app (G.op.obj V)) H₁
    dsimp at hh
    erw [← Category.assoc (ψ.hom.app (G.op.obj V))
      (c.hom.hom.app ((proEtaleBaseChange U.hom).op.obj (G.op.obj V)))
      (R.obj.map (G.map (a.unit.app V.unop)).op), ← hh]
    rw [← Functor.map_comp, ← op_comp]
    erw [a.left_triangle_components]
    change c.hom.hom.app V ≫ R.obj.map (𝟙 (G.op.obj V)) = c.hom.hom.app V
    rw [R.obj.map_id]
    exact Category.comp_id (c.hom.hom.app V)
  let d := SheafOfModules.pushforwardPushforwardAdj a c.hom ψ H₁ H₂
  have z := proEtaleModuleInverseImageAdjunction U.hom A
  let z' : proEtaleModuleInverseImage U.hom A ⊣ SheafOfModules.pushforward.{u + 1} ψ :=
    z.ofNatIsoRight (SheafOfModules.pushforwardCongr (by
      simp [ψ, proEtaleRingDirectImageMap]))
  let e := z'.leftAdjointUniq d
  let t : SheafOfModules.overFunctor.{u + 1} R U ⋙ q.functor ≅
      SheafOfModules.pushforward.{u + 1} c.hom :=
    Functor.fullyFaithfulCancelRight (SheafOfModules.forget S) (eqToIso (by
      change SheafOfModules.overFunctor R U ⋙ (q.functor ⋙ SheafOfModules.forget S) = _
      rw [hq]
      rfl))
  refine ⟨q.symm, ⟨?_⟩⟩
  exact Functor.isoWhiskerRight (e ≪≫ t.symm) q.inverse ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (SheafOfModules.overFunctor R U) q.unitIso.symm ≪≫
    Functor.rightUnitor _

end AlgebraicGeometry.Scheme

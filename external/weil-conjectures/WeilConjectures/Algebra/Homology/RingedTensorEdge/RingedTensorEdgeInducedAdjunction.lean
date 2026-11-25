/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.RingedTensorCorner.ProjectionMateExact
public import WeilConjectures.CategoryTheory.RingedToposRingData
public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import Mathlib.Algebra.Category.Ring.Limits
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.SixFunctors.Supporting.Tensor.SuppliedTensorAdjunctionNormalization
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # The induced module direct image of a supplied tensor edge

Source: Stacks Project, Modules on Sites, Tag 03D7
(blueprint: lem-sbc-ringed-tensor-edge-induced-adjunction).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace SheafOfModules

/-- The structural ring map of a tensor edge, retaining the given geometric adjunction.
Source: Stacks 03D7 (blueprint: lem-sbc-ringed-tensor-edge-induced-adjunction). -/
def RingedTensorEdge.ringData {Y X : RingedTensorCorner.{u, w}} (e : RingedTensorEdge Y X) :
    RingedToposMorphism.RingData
      ((sheafCompose X.topology (forget₂ CommRingCat RingCat)).obj X.ring)
      ((sheafCompose Y.topology (forget₂ CommRingCat RingCat)).obj Y.ring) where
  inverse := e.inverse
  direct := e.direct
  adj := e.adjunction
  leftExact := inferInstance
  ringMap := e.algebraic.ringUnderlying.hom ≫
    (sheafCompose X.topology (CategoryTheory.forget CommRingCat)).map e.ringMap
  ring_zero := by
    intro T z hz U t
    change T ⟶ (sheafCompose Y.topology (CategoryTheory.forget CommRingCat)).obj Y.ring at z
    change (e.ringMap.hom.app U).hom
      (e.algebraic.ringUnderlying.hom.hom.app U ((e.inverse.map z).hom.app U t)) = 0
    simpa only [id_eq, map_zero] using
      congrArg (e.ringMap.hom.app U).hom (e.algebraic.ringZero T z hz U t)
  ring_one := by
    intro T z hz U t
    change T ⟶ (sheafCompose Y.topology (CategoryTheory.forget CommRingCat)).obj Y.ring at z
    change (e.ringMap.hom.app U).hom
      (e.algebraic.ringUnderlying.hom.hom.app U ((e.inverse.map z).hom.app U t)) = 1
    simpa only [id_eq, map_one] using
      congrArg (e.ringMap.hom.app U).hom (e.algebraic.ringOne T z hz U t)
  ring_add := by
    intro T x y z hz U t
    change T ⟶ (sheafCompose Y.topology (CategoryTheory.forget CommRingCat)).obj Y.ring at x y z
    change (e.ringMap.hom.app U).hom
      (e.algebraic.ringUnderlying.hom.hom.app U ((e.inverse.map z).hom.app U t)) =
      (e.ringMap.hom.app U).hom
        (e.algebraic.ringUnderlying.hom.hom.app U ((e.inverse.map x).hom.app U t)) +
      (e.ringMap.hom.app U).hom
        (e.algebraic.ringUnderlying.hom.hom.app U ((e.inverse.map y).hom.app U t))
    simpa only [id_eq, map_add] using
      congrArg (e.ringMap.hom.app U).hom (e.algebraic.ringAdd T x y z hz U t)
  ring_mul := by
    intro T x y z hz U t
    change T ⟶ (sheafCompose Y.topology (CategoryTheory.forget CommRingCat)).obj Y.ring at x y z
    change (e.ringMap.hom.app U).hom
      (e.algebraic.ringUnderlying.hom.hom.app U ((e.inverse.map z).hom.app U t)) =
      (e.ringMap.hom.app U).hom
        (e.algebraic.ringUnderlying.hom.hom.app U ((e.inverse.map x).hom.app U t)) *
      (e.ringMap.hom.app U).hom
        (e.algebraic.ringUnderlying.hom.hom.app U ((e.inverse.map y).hom.app U t))
    simpa only [id_eq, map_mul] using
      congrArg (e.ringMap.hom.app U).hom (e.algebraic.ringMul T x y z hz U t)

/-- The specified scalar-extension pullback is adjoint to the induced module direct image.
The comparison with the edge's supplied right adjoint preserves both unit and counit,
and the induced adjunction is normalized on underlying sheaves by scalar insertion.

Source: Stacks Project, Modules on Sites, Tag 03D7
(blueprint: lem-sbc-ringed-tensor-edge-induced-adjunction).

Proof: compose the algebraic inverse image's ring identification with the structural
ring homomorphism. Apply the induced-module construction to this ring datum. The
normalized supplied-tensor adjunction applies because cancellation of the ring
identification gives its required structural-map equation. Finally uniqueness of right
adjoints gives the comparison and its unit and counit equations. -/
theorem RingedTensorEdge.inducedModuleAdjunction
    {Y X : RingedTensorCorner.{u, w}} (e : RingedTensorEdge Y X) :
    ∃ m : e.ringData.Modules,
    ∃ am : e.pullback ⊣ m.modules,
    ∃ t : e.pushforward ≅ m.modules,
      (∀ (M : Y.mateModules) (H : X.mateModules) (v : e.pullback.obj M ⟶ H),
        (SheafOfModules.toSheaf _ ⋙
          sheafCompose Y.topology (CategoryTheory.forget AddCommGrpCat)).map
            (am.homEquiv M H v) ≫ m.underlying.hom.app H =
          e.adjunction.homEquiv _ _ (e.insertion M ≫
            (SheafOfModules.toSheaf _ ⋙
              sheafCompose X.topology (CategoryTheory.forget AddCommGrpCat)).map v)) ∧
      (∀ M, e.moduleAdjunction.unit.app M ≫ t.hom.app (e.pullback.obj M) =
        am.unit.app M) ∧
      (∀ H, e.pullback.map (t.hom.app H) ≫ am.counit.app H =
        e.moduleAdjunction.counit.app H) := by
  obtain ⟨m⟩ := ringData_inducedModules X.ring Y.ring e.ringData
  let f := e.ringData.withModules m
  have hc : (sheafCompose X.topology (CategoryTheory.forget CommRingCat)).map e.ringMap =
      e.algebraic.ringUnderlying.inv ≫ f.ringMap := by
    dsimp [f, RingedTensorEdge.ringData, RingedToposMorphism.RingData.withModules]
    simp only [Iso.inv_hom_id_assoc]
  obtain ⟨am, hm⟩ := suppliedTensorAdjunction_normalized f e.inverseRing e.algebraic
    e.ringMap hc e.pullback e.object_eq e.map_eq e.ordinaryTensor
  exact ⟨m, am, Adjunction.rightAdjointUniq e.moduleAdjunction am, hm,
    Adjunction.unit_rightAdjointUniq_hom_app e.moduleAdjunction am,
    Adjunction.rightAdjointUniq_hom_app_counit e.moduleAdjunction am⟩

end SheafOfModules

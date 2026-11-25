/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import all WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import WeilConjectures.AlgebraicGeometry.SplitProEtaleAbelianProductMap

/-! # The canonical product map over a split finite cover -/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem moduleCounit_forget
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U : Scheme.{u}} (p : U ⟶ X)
    (N : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)) :
    ((upperStarLowerStarAdjunction Λ p).counit.app N).hom =
      (profinitePointModuleForgetPullbackIso Λ p).hom.app ((lowerStar Λ p).obj N) ≫
        (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} p).counit.app N.X := by
  let c := profinitePointModuleForgetPullbackIso Λ p
  let a := ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} p
  let aM := upperStarLowerStarAdjunction Λ p
  apply (cancel_epi (c.inv.app ((lowerStar Λ p).obj N))).1
  change c.inv.app ((lowerStar Λ p).obj N) ≫ (aM.counit.app N).hom =
    c.inv.app ((lowerStar Λ p).obj N) ≫ c.hom.app ((lowerStar Λ p).obj N) ≫
      a.counit.app N.X
  rw [Iso.inv_hom_id_app_assoc]
  apply (a.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  have hu := ProEtale.moduleUnit_forget_inv Λ p ((lowerStar Λ p).obj N)
  change a.unit.app ((ProEtale.lowerStar Ab.{u + 1} p).obj N.X) ≫
    (ProEtale.lowerStar Ab.{u + 1} p).map (c.inv.app ((lowerStar Λ p).obj N)) =
      (aM.unit.app ((lowerStar Λ p).obj N)).hom at hu
  have ht := congrArg (fun z ↦ z.hom) (aM.right_triangle_components N)
  change (aM.unit.app ((lowerStar Λ p).obj N)).hom ≫
    (ProEtale.lowerStar Ab.{u + 1} p).map (aM.counit.app N).hom = 𝟙 _ at ht
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z ↦ z ≫
      (ProEtale.lowerStar Ab.{u + 1} p).map (aM.counit.app N).hom) hu).trans
        (ht.trans (a.right_triangle_components N.X).symm))

private theorem moduleComparison_forget
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U Y : Scheme.{u}} (p : U ⟶ X)
    (t : Y ⟶ U) (g : Y ⟶ X) (w : t ≫ p = g)
    (K : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (((eqToIso (congrArg (upperStar Λ) w)).symm ≪≫ upperStarComp Λ t p).hom.app K).hom ≫
      (profinitePointModuleForgetPullbackIso Λ t).hom.app ((upperStar Λ p).obj K) ≫
      (ProEtale.upperStar Ab.{u + 1} t).map
        ((profinitePointModuleForgetPullbackIso Λ p).hom.app K) =
    (profinitePointModuleForgetPullbackIso Λ g).hom.app K ≫
      ((eqToIso (congrArg (ProEtale.upperStar Ab.{u + 1}) w)).symm ≪≫
        ProEtale.upperStarComp Ab.{u + 1} t p).hom.app K.X := by
  subst g
  simpa only [eqToIso_refl, Iso.refl_symm, Iso.refl_trans, Mod.forget] using
    (profinite_point_pullback_module_comparison Λ).2.2 Y U X t p K

private theorem moduleSheetMap_forget
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U Y : Scheme.{u}} (p : U ⟶ X)
    (t : Y ⟶ U) (g : Y ⟶ X) (w : t ≫ p = g)
    (N : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)) :
    (((eqToIso (congrArg (upperStar Λ) w)).symm ≪≫ upperStarComp Λ t p).hom.app
        ((lowerStar Λ p).obj N) ≫
      (upperStar Λ t).map ((upperStarLowerStarAdjunction Λ p).counit.app N)).hom ≫
        (profinitePointModuleForgetPullbackIso Λ t).hom.app N =
    (profinitePointModuleForgetPullbackIso Λ g).hom.app ((lowerStar Λ p).obj N) ≫
      ((eqToIso (congrArg (ProEtale.upperStar Ab.{u + 1}) w)).symm ≪≫
        ProEtale.upperStarComp Ab.{u + 1} t p).hom.app
          ((ProEtale.lowerStar Ab.{u + 1} p).obj N.X) ≫
      (ProEtale.upperStar Ab.{u + 1} t).map
        ((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} p).counit.app N.X) := by
  subst g
  simp only [eqToIso_refl, Iso.refl_symm, Iso.refl_trans]
  let c := profinitePointModuleForgetPullbackIso Λ t
  let ε := (upperStarLowerStarAdjunction Λ p).counit.app N
  have hn := c.hom.naturality ε
  change ((upperStar Λ t).map ε).hom ≫ c.hom.app N =
    c.hom.app ((upperStar Λ p).obj ((lowerStar Λ p).obj N)) ≫
      (ProEtale.upperStar Ab.{u + 1} t).map ε.hom at hn
  simp only [Mod.comp_hom', Category.assoc]
  rw [hn, moduleCounit_forget Λ p N, Functor.map_comp]
  have hc := moduleComparison_forget Λ p t (t ≫ p) rfl ((lowerStar Λ p).obj N)
  simp only [eqToIso_refl, Iso.refl_symm, Iso.refl_trans] at hc
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun z ↦ z ≫
      (ProEtale.upperStar Ab.{u + 1} t).map
        ((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} p).counit.app N.X)) hc)

private theorem moduleProduct_from_abelian
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U Y : Scheme.{u}} (p : U ⟶ X)
    (g : Y ⟶ X) (n : ℕ) (t : Fin n → (Y ⟶ U)) (w : ∀ j, t j ≫ p = g)
    (N : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))
    (hq : IsIso (Pi.lift (fun j ↦
      ((eqToIso (congrArg (ProEtale.upperStar Ab.{u + 1}) (w j))).symm ≪≫
        ProEtale.upperStarComp Ab.{u + 1} (t j) p).hom.app
          ((ProEtale.lowerStar Ab.{u + 1} p).obj N.X) ≫
      (ProEtale.upperStar Ab.{u + 1} (t j)).map
        ((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} p).counit.app N.X)))) :
    IsIso (Pi.lift (fun j ↦
      ((eqToIso (congrArg (upperStar Λ) (w j))).symm ≪≫
        upperStarComp Λ (t j) p).hom.app ((lowerStar Λ p).obj N) ≫
      (upperStar Λ (t j)).map ((upperStarLowerStarAdjunction Λ p).counit.app N))) := by
  classical
  let V : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y) ⥤ Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1} :=
    Mod.forget (condensedRingObj Λ Y)
  let B := fun j ↦ (upperStar Λ (t j)).obj N
  let qM := Pi.lift (fun j ↦
    ((eqToIso (congrArg (upperStar Λ) (w j))).symm ≪≫
      upperStarComp Λ (t j) p).hom.app ((lowerStar Λ p).obj N) ≫
    (upperStar Λ (t j)).map ((upperStarLowerStarAdjunction Λ p).counit.app N))
  let qA := Pi.lift (fun j ↦
    ((eqToIso (congrArg (ProEtale.upperStar Ab.{u + 1}) (w j))).symm ≪≫
      ProEtale.upperStarComp Ab.{u + 1} (t j) p).hom.app
        ((ProEtale.lowerStar Ab.{u + 1} p).obj N.X) ≫
    (ProEtale.upperStar Ab.{u + 1} (t j)).map
      ((ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} p).counit.app N.X))
  let e : V.obj (∏ᶜ B) ≅ ∏ᶜ (fun j ↦ (ProEtale.upperStar Ab.{u + 1} (t j)).obj N.X) :=
    PreservesProduct.iso V B ≪≫
      Pi.mapIso (fun j ↦ (profinitePointModuleForgetPullbackIso Λ (t j)).app N)
  have he : V.map qM ≫ e.hom =
      (profinitePointModuleForgetPullbackIso Λ g).hom.app ((lowerStar Λ p).obj N) ≫
        qA := by
    apply Pi.hom_ext
    intro j
    simp only [e, B, Iso.trans_hom, Category.assoc, Pi.mapIso_hom_π,
      PreservesProduct.iso_hom, piComparison_comp_π_assoc, qA]
    rw [← Category.assoc, ← V.map_comp]
    dsimp only [qM, qA]
    erw [Pi.lift_comp_π, Pi.lift_comp_π]
    simpa only [V, Mod.forget, Functor.comp_obj, Iso.app_hom, Iso.trans_hom] using
      moduleSheetMap_forget Λ p (t j) g (w j) N
  have : IsIso qA := hq
  have : IsIso (V.map qM ≫ e.hom) := he.symm ▸ inferInstance
  have : IsIso (V.map qM) := by
    have hx : V.map qM = (V.map qM ≫ e.hom) ≫ e.inv := by simp
    rw [hx]
    infer_instance
  exact isIso_of_reflects_iso qM V

/-- The counit maps to the sheets of a split finite cover form an isomorphism.

Source: Stacks Project, Tag 095B, proof by sections over a split finite cover; the
weakly etale base-change argument for the pro-etale site.
(auxiliary; not a blueprint node)

Proof in words. Compute inverse image along the weakly etale map g by restriction
along the localization functor of pro-etale sites. For a test W over Y, the assumed
coproduct decomposition, after base change to W, decomposes W times_X U into n
open-and-closed copies of W. The counit on the j-th sheet is the restriction to
that copy. The sheaf condition identifies sections on their disjoint union with
the finite product of their sections: distinct overlaps are empty, and on a
self-overlap the two restrictions agree. This also proves the empty case.
The module maps displayed here are linear because they are composites of the
module inverse-image comparison and the module counit. Forgetting the module
actions identifies them with those restriction maps, using the forgetful
inverse-image comparison, its composition coherence, and the adjunction triangle
identities. Module forgetful functors create products and reflect isomorphisms,
so the product map is invertible. -/
theorem splitProEtaleModuleProductMap_isIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U Y : Scheme.{u}} (p : U ⟶ X)
    (g : Y ⟶ X) [WeaklyEtale g]
    (n : ℕ) (t : Fin n → (Y ⟶ U)) (w : ∀ j, t j ≫ p = g)
    (hc : Nonempty (IsColimit (Cofan.mk (pullback p g)
      (fun j ↦ pullback.lift (t j) (𝟙 Y) (by simpa using w j)))))
    (N : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)) :
    let a := fun j ↦ (eqToIso (congrArg (upperStar Λ) (w j))).symm ≪≫
      upperStarComp Λ (t j) p
    IsIso (Pi.lift (fun j ↦
      (a j).hom.app ((lowerStar Λ p).obj N) ≫
        (upperStar Λ (t j)).map ((upperStarLowerStarAdjunction Λ p).counit.app N))) := by
  exact moduleProduct_from_abelian Λ p g n t w N
    (splitProEtaleAbelianProductMap_isIso p g n t w hc N.X)

end AlgebraicGeometry.ProEtale.CondensedRing

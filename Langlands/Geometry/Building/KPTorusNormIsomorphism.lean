import Langlands.Geometry.Building.KPTorusNormNaturality

/-! # Isomorphism invariance of torus norm subgroups with a common field -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj

namespace Langlands.Geometry.Building

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [FiniteDimensional k L] [IsGalois k L]
  {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation L Γ₀)
  {T U : CommGroupScheme (Spec (CommRingCat.of k))}
  [IsAffine T.X.left] [IsAffine U.X.left]

/-- An isomorphism carries the norm subgroup onto the norm subgroup when the
extension and valuation are the same. -/
theorem map_torusNormIwahori_eq_of_iso (e : T.toGrp ≅ U.toGrp) :
    (torusNormIwahori k L v T).map (rationalPoints.map e.hom) =
      torusNormIwahori k L v U := by
  refine le_antisymm (map_torusNormIwahori_le k L v (Additive.ofMul e.hom)) ?_
  intro y hy
  refine ⟨rationalPoints.map e.inv y,
    map_torusNormIwahori_le k L v (Additive.ofMul e.inv) ⟨y, hy, rfl⟩, ?_⟩
  simp only [rationalPoints.map_apply, Category.assoc, ← Grp.comp_hom_hom,
    e.inv_hom_id, Grp.id_hom_hom, Category.comp_id]

/-- The isomorphism of norm subgroups induced by an isomorphism of affine
commutative group schemes over the same extension and valuation. -/
def torusNormIwahoriEquiv (e : T.toGrp ≅ U.toGrp) :
    torusNormIwahori k L v T ≃* torusNormIwahori k L v U :=
  ((isoPointsEquiv e (Over.mk (𝟙 _))).subgroupMap (torusNormIwahori k L v T)).trans
    (MulEquiv.subgroupCongr (map_torusNormIwahori_eq_of_iso k L v e))

@[simp]
theorem coe_torusNormIwahoriEquiv_apply (e : T.toGrp ≅ U.toGrp)
    (x : torusNormIwahori k L v T) :
    (torusNormIwahoriEquiv k L v e x : rationalPoints U.toGrp) =
      rationalPoints.map e.hom x :=
  rfl

/-- Compatible embeddings of isomorphic sources have the same ambient norm
subgroup when the extension and valuation are the same. -/
theorem map_torusNormIwahori_eq_of_iso_comp
    {H : GroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ H) (j : U.toGrp ⟶ H) (e : T.toGrp ≅ U.toGrp)
    (he : e.hom ≫ j = i) :
    (torusNormIwahori k L v T).map (rationalPoints.map i) =
      (torusNormIwahori k L v U).map (rationalPoints.map j) := by
  have hm : rationalPoints.map i = (rationalPoints.map j).comp (rationalPoints.map e.hom) := by
    ext x
    simp only [MonoidHom.comp_apply, rationalPoints.map_apply, Category.assoc,
      ← Grp.comp_hom_hom, he]
  rw [hm, ← Subgroup.map_map, map_torusNormIwahori_eq_of_iso]

namespace UnramifiedZeroDatum

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {H H' : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))}

/-- Data using the same splitting field have compatible torus norm subgroups
under any isomorphism of their tori. -/
theorem torusIwahori_map_eq_of_iso_of_field_eq
    (E : UnramifiedZeroDatum F H) (E' : UnramifiedZeroDatum F H')
    (e : E.T.toGrp ≅ E'.T.toGrp) (hL : E.L = E'.L) :
    E.torusIwahori.map (rationalPoints.map e.hom) = E'.torusIwahori := by
  have hn (L₁ L₂ : IntermediateField (UnramifiedClosure F) (SeparableClosure F))
      [FiniteDimensional (UnramifiedClosure F) L₁] [IsGalois (UnramifiedClosure F) L₁]
      [FiniteDimensional (UnramifiedClosure F) L₂] [IsGalois (UnramifiedClosure F) L₂]
      (h : L₁ = L₂) :
      torusNormIwahori (UnramifiedClosure F) L₁ (intermediateValuation F L₁) E'.T =
        torusNormIwahori (UnramifiedClosure F) L₂ (intermediateValuation F L₂) E'.T := by
    subst L₂
    rfl
  exact (map_torusNormIwahori_eq_of_iso (UnramifiedClosure F) E.L
    (intermediateValuation F E.L) e).trans (hn E.L E'.L hL)

end UnramifiedZeroDatum

end Langlands.Geometry.Building

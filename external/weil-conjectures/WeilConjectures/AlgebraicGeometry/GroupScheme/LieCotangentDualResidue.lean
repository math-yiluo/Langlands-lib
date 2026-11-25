/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Ring
public import Mathlib.AlgebraicGeometry.ResidueField
@[expose] public section
universe u
open CategoryTheory
open scoped MonObj
namespace AlgebraicGeometry.GrpObj
set_option backward.isDefEq.respectTransparency false
/-- The structural residue map at the identity is bijective.
Source: blueprint `proposition-cartier-s-theorem`, the rationality of the identity point. -/
theorem identity_residue_rational
    {k : Type u} [Field k] (G : Over (Spec (.of k))) [GrpObj G] :
    let x := unitSection G (IsLocalRing.closedPoint k)
    let a := StructureSheaf.toStalk k (G.hom x) ≫ G.hom.stalkMap x ≫ G.left.residue x
    Function.Bijective a.hom ∧
      Spec.map a ≫ unitSection G = G.left.fromSpecResidueField x := by
  let x := unitSection G (IsLocalRing.closedPoint k)
  let a := StructureSheaf.toStalk k (G.hom x) ≫ G.hom.stalkMap x ≫ G.left.residue x
  let b := G.left.descResidueField (Scheme.stalkClosedPointTo (unitSection G))
  have hab : a ≫ b = 𝟙 (CommRingCat.of k) := by
    dsimp [a, b, x]
    rw [Category.assoc, Category.assoc, Scheme.residue_descResidueField]
    rw [← Scheme.stalkClosedPointTo_comp]
    change StructureSheaf.toStalk k
      ((unitSection G ≫ G.hom) (IsLocalRing.closedPoint k)) ≫
      Scheme.stalkClosedPointTo (unitSection G ≫ G.hom) = _
    have h (f : Spec (.of k) ⟶ Spec (.of k)) (hf : f = 𝟙 _) :
        StructureSheaf.toStalk k (f (IsLocalRing.closedPoint k)) ≫
          Scheme.stalkClosedPointTo f = 𝟙 (CommRingCat.of k) := by
      subst f
      simp only [Scheme.stalkClosedPointTo, Scheme.Hom.stalkMap_id,
        Scheme.Hom.id_base, TopCat.hom_id, ContinuousMap.id_apply, Category.id_comp]
      change StructureSheaf.toStalk (CommRingCat.of k)
        (IsLocalRing.closedPoint (CommRingCat.of k)) ≫
        (stalkClosedPointIso (CommRingCat.of k)).hom = _
      rw [← stalkClosedPointIso_inv (CommRingCat.of k)]
      exact (stalkClosedPointIso (CommRingCat.of k)).inv_hom_id
    exact h _ (unitSection_comp_hom G)
  have ha : Function.Bijective a.hom := by
    refine ⟨a.hom.injective, ?_⟩
    intro y
    refine ⟨b.hom y, b.hom.injective ?_⟩
    exact congrArg (fun f : CommRingCat.of k ⟶ CommRingCat.of k ↦ f.hom (b.hom y)) hab
  have hba : b ≫ a = 𝟙 _ := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro y
    apply b.hom.injective
    exact congrArg (fun f : CommRingCat.of k ⟶ CommRingCat.of k ↦ f.hom (b.hom y)) hab
  refine ⟨ha, ?_⟩
  calc
    Spec.map a ≫ unitSection G =
        Spec.map a ≫ Spec.map b ≫ G.left.fromSpecResidueField x := by
      rw [Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField]
    _ = G.left.fromSpecResidueField x := by
      rw [← Spec.map_comp_assoc, hba, Spec.map_id, Category.id_comp]
end AlgebraicGeometry.GrpObj

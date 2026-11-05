import Langlands.GroupScheme.Lie.AdjointDeterminantCharacter
import Langlands.GroupScheme.Reductive.CentralDerivedProductStatement

/-! # Triviality of the actual reductive adjoint determinant -/

noncomputable section

set_option maxRecDepth 2048
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Lie

/-- The actual rational adjoint determinant is zero for every connected reductive
affine finite-type field group, with no splitness or dimension assumption. -/
def ConnectedReductiveAdjointDeterminantStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G → adjointDeterminantCharacter G = 0

variable {k : Type u} [Field k]
  (G : GroupScheme (Spec (CommRingCat.of k)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

omit [LocallyOfFiniteType G.X.hom] in
/-- All-test centrality makes conjugation the identity on the actual Lie kernel. -/
theorem differential_conjugation_eq_refl_of_isCentral
    {Z : GroupScheme (Spec (CommRingCat.of k))} (i : Z ⟶ G) (hi : IsCentral i)
    (A : CommAlgCat.{u} (CommRingCat.of k)) (z : Z.affinePoints A) :
    (AutomorphicAction.conjugation (𝟙 G)).differential (z ≫ i.hom.hom) =
      LinearEquiv.refl A (Additive (lieKernel G A)) := by
  apply LinearEquiv.ext
  intro x
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [AutomorphicAction.differential_val, AutomorphicAction.conjugation_act]
  simp only [Grp.id_hom_hom, Category.comp_id]
  have hc : Commute (constant G (z ≫ i.hom.hom)) x.toMul.val := by
    simpa only [constant, affineMap_apply, Category.assoc] using
      commute_of_mem_center (hi _ (constant Z z)) x.toMul.val
  rw [hc.eq, mul_inv_cancel_right]
  rfl

/-- The adjoint determinant is zero on every affine central subgroup. -/
theorem adjointDeterminantCharacter_restrict_eq_zero_of_isCentral
    {Z : GroupScheme (Spec (CommRingCat.of k))} [IsAffine Z.X.left]
    (i : Z ⟶ G) (hi : IsCentral i) :
    characterRestrict i (adjointDeterminantCharacter G) = 0 := by
  have hv (A : CommAlgCat.{u} (CommRingCat.of k)) (z : Z.affinePoints A) :
      z ≫ (characterRestrict i (adjointDeterminantCharacter G)).toMul.hom.hom =
        (1 : (algSpec (CommRingCat.of k)).obj (op A) ⟶
          (GroupScheme.Gm (Spec (CommRingCat.of k))).X) := by
    apply (Gm.affinePointsEquiv _).injective
    change Gm.affinePointsEquiv ((algSpec (CommRingCat.of k)).obj (op A)).hom
      (z ≫ (i ≫ (adjointDeterminantCharacter G).toMul).hom.hom) = _
    rw [Grp.comp_hom_hom, ← Category.assoc,
      adjointDeterminantCharacter_affinePoints,
      differential_conjugation_eq_refl_of_isCentral G i hi]
    simp only [LinearEquiv.det_refl, map_one]
  let e := AffineCoordinates.groupSchemeIso Z
  have hx := hv (AffineCoordinates.algebra Z) e.hom.hom.hom
  apply Additive.toMul.injective
  apply Grp.hom_ext
  have key : e.inv.hom.hom ≫ e.hom.hom.hom = 𝟙 Z.X := by
    rw [← Grp.comp_hom_hom, Iso.inv_hom_id, Grp.id_hom_hom]
  calc
    (characterRestrict i (adjointDeterminantCharacter G)).toMul.hom.hom =
        e.inv.hom.hom ≫
          (e.hom.hom.hom ≫
            (characterRestrict i (adjointDeterminantCharacter G)).toMul.hom.hom) := by
              rw [← Category.assoc, key, Category.id_comp]
    _ = e.inv.hom.hom ≫ 1 := by rw [hx]
    _ = _ := by
      rw [MonObj.comp_one]
      rfl

/-- The central-times-derived epimorphism reduces the reductive assertion to
central triviality and the already proved annihilation of derived subgroups. -/
theorem connectedReductiveAdjointDeterminant_of_centralDerivedProduct
    (hprod : ReductiveCentralDerivedProductStatement.{u}) :
    ConnectedReductiveAdjointDeterminantStatement.{u} := by
  intro k _ G _ _ hG
  obtain ⟨Z, D, i, d, hZa, _, _, _, hi, hd, hepi⟩ := hprod k G hG
  let : IsAffineHom Z.toGrp.X.hom := hZa
  let : IsAffine Z.toGrp.X.left := isAffine_of_isAffineHom Z.toGrp.X.hom
  let : Epi (subgroupProductMap i d) := hepi
  apply Additive.toMul.injective
  exact comp_eq_one_of_epi_subgroupProductMap i d
    (adjointDeterminantCharacter G).toMul
    (congrArg Additive.toMul
      (adjointDeterminantCharacter_restrict_eq_zero_of_isCentral G i hi))
    (congrArg Additive.toMul
      (hd.characterRestrict_eq_zero (adjointDeterminantCharacter G)))

end Langlands.GroupScheme.Lie

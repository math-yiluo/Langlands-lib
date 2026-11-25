/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Supported.SupportedCupFunctorialityModels
import all WeilConjectures.AlgebraicGeometry.Supported.SupportedCup
/-! # Naturality of normalized coefficient multiplication

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
cor-pur-affine-space-zero-section-purity.proof.md, ordered exterior products
(blueprint: lem-pur-coordinate-coefficient-support-naturality).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
attribute [local instance] CategoryTheory.Sheaf.monoidalCategory
  CategoryTheory.Sheaf.braidedCategory
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry WeilConjectures
namespace AlgebraicGeometry.ProEtale.AffineZeroPurity
private theorem support_map_normalized (P : PurityFiniteSetting.{u})
    {C D X : Scheme.{u}} (i : C ⟶ X) (j : D ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion j] (g : D ⟶ C) (hg : g ≫ i = j) :
    cupCoefficientRestriction P i ≫ P.functorialCupSupportMap true i j g hg =
      cupCoefficientRestriction P j :=
  (P.functorialCupSupportMap_existsUnique true i j g hg).choose_spec.1
/-- Multiplication of supported constants is natural in its first closed support.
Source: restriction normalization in the affine-space exterior-product argument.
(blueprint: lem-pur-coordinate-coefficient-support-naturality).

Proof: the tensor of the two constant restriction maps is epic. Precompose both
proposed maps with it. The left composite is normalized coefficient multiplication
followed by restriction to the new intersection. On the right, tensor functoriality
and normalization of the first support map give the same expression by the
normalization of the new coefficient multiplication. Cancel the epic map. -/
theorem coordinate_coefficient_support_naturality (P : PurityFiniteSetting.{u})
    {Z Z' W X : Scheme.{u}} (i : Z ⟶ X) (i' : Z' ⟶ X) (j : W ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion i'] [IsClosedImmersion j]
    (g : Z' ⟶ Z) (hg : g ≫ i = i')
    (q : pullback i' j ⟶ pullback i j)
    (hq : q ≫ cupIntersection i j = cupIntersection i' j) :
    cupCoefficientMap P i j ≫ P.functorialCupSupportMap true
        (cupIntersection i j) (cupIntersection i' j) q hq =
      (P.functorialCupSupportMap true i i' g hg ⊗ₘ 𝟙 _) ≫
        cupCoefficientMap P i' j := by
  have : Epi (cupCoefficientRestriction P i) := cupRestriction_epi P i
  have : Epi (cupCoefficientRestriction P j) := cupRestriction_epi P j
  have : Epi (cupCoefficientRestriction P i ▷ P.constant X) :=
    (tensorRight _).map_epi _
  have : Epi ((lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj
      (P.constant Z) ◁ cupCoefficientRestriction P j) := (tensorLeft _).map_epi _
  have : Epi (cupCoefficientRestriction P i ⊗ₘ cupCoefficientRestriction P j) := by
    rw [MonoidalCategory.tensorHom_def]
    infer_instance
  let t : (lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj (P.constant Z) ⟶
      (lowerStar (ModuleCat.{u + 1} P.Coefficient) i').obj (P.constant Z') :=
    P.functorialCupSupportMap true i i' g hg
  let v : (lowerStar (ModuleCat.{u + 1} P.Coefficient) (cupIntersection i j)).obj
      (P.constant (pullback i j)) ⟶
      (lowerStar (ModuleCat.{u + 1} P.Coefficient) (cupIntersection i' j)).obj
      (P.constant (pullback i' j)) :=
    P.functorialCupSupportMap true (cupIntersection i j) (cupIntersection i' j) q hq
  have hi := support_map_normalized P i i' g hg
  have hq' := support_map_normalized P (cupIntersection i j) (cupIntersection i' j) q hq
  change cupCoefficientRestriction P i ≫ t = cupCoefficientRestriction P i' at hi
  change cupCoefficientRestriction P (cupIntersection i j) ≫ v =
    cupCoefficientRestriction P (cupIntersection i' j) at hq'
  have hμ := (cupCoefficientMap_existsUnique P i j).exists.choose_spec
  have hμ' := (cupCoefficientMap_existsUnique P i' j).exists.choose_spec
  change (cupCoefficientRestriction P i ⊗ₘ cupCoefficientRestriction P j) ≫
    cupCoefficientMap P i j = _ at hμ
  change (cupCoefficientRestriction P i' ⊗ₘ cupCoefficientRestriction P j) ≫
    cupCoefficientMap P i' j = _ at hμ'
  change cupCoefficientMap P i j ≫ v = (t ⊗ₘ 𝟙 _) ≫ cupCoefficientMap P i' j
  apply (cancel_epi (cupCoefficientRestriction P i ⊗ₘ cupCoefficientRestriction P j)).mp
  rw [← Category.assoc, hμ, Category.assoc, hq']
  rw [← Category.assoc _ (_ ⊗ₘ _), tensorHom_comp_tensorHom]
  simp only [Category.comp_id, hi]
  exact hμ'.symm
end AlgebraicGeometry.ProEtale.AffineZeroPurity

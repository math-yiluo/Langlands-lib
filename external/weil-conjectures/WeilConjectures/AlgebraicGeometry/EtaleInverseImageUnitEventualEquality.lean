/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.AlgebraicGeometry.EtaleAbelianUnitEqualOpen
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-! # Eventual equality for a single inverse-image unit

Source: Stacks Project, Sites Tag 0A35 and Etale Cohomology Tag 09YQ.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

/-- Equality under the inverse-image unit for one stage sheaf is detected by
an inverse-image unit at a later scheme stage.
Source: Stacks Project, Sites Tag 0A35 (lemma-compute-pullback-to-limit),
and Etale Cohomology Tags 0EYL, 04HR and 09YQ.
(blueprint: lem-weil-pbc-etale-inverse-image-unit-eventual-equality).

Proof: Restrict the system to the cofinal directed tail above i. Cover U by
finitely many affine opens. The affine transition maps preserve affineness after
base change. Present the limit affine etale site by the filtered colimit of
stage affine etale sites (0EYL). Restriction to this basis is an equivalence of
sheaf categories (04HR). The inverse-image section formula of 0A35, applied to
this single sheaf, identifies the limit unit images with images of the original
sections in the filtered colimit of sections of its stage inverse images.
Equality of these images is witnessed at a later stage. The adjunction unit
formula identifies the witness maps with the displayed units. Do this on each
of the finitely many affine opens, choose a common later stage, and use unit
naturality and separatedness on the pulled-back cover to obtain equality on U.
This does not involve any colimit of varying sheaves. For empty U the sheaf
condition for the empty covering gives equality already at i; a zero sheaf and
a singleton directed index satisfy the same argument. -/
theorem etale_inverse_image_unit_eventual_equality
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ (i j : Iᵒᵖ) (f : i ⟶ j), IsAffineHom (D.map f)]
    (i : I) (F : Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (U : (D.obj (op i)).Etale) [CompactSpace U.left] [QuasiSeparatedSpace U.left]
    (s t : F.obj.obj (op U))
    (hst : ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
        (c.π.app (op i))).unit.app F).hom.app (op U) s =
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
        (c.π.app (op i))).unit.app F).hom.app (op U) t) :
    ∃ (k : I) (a : i ⟶ k),
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
        (D.map a.op)).unit.app F).hom.app (op U) s =
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
        (D.map a.op)).unit.app F).hom.app (op U) t := by
  have : ∀ {j k : Iᵒᵖ} (a : j ⟶ k), IsAffineHom (D.map a) :=
    fun a ↦ inferInstance
  obtain ⟨W, hW⟩ := etale_abelian_unit_equal_open (D.obj (op i)) F U s t
  have : CompactSpace ↥((𝟭 Scheme).obj U.left) :=
    inferInstanceAs (CompactSpace U.left)
  let B := baseChangeDiagram D U.hom
  let b := baseChangeCone D c U.hom
  let j₀ : Over (op i) := Over.mk (𝟙 (op i))
  let f₀ := pullback.fst U.hom (D.map j₀.hom)
  have : ∀ j, CompactSpace (B.obj j) := fun j ↦
    inferInstanceAs (CompactSpace ((baseChangeDiagram D U.hom).obj j))
  have hlimit : b.π.app j₀ ⁻¹ᵁ (f₀ ⁻¹ᵁ W) = ⊤ := by
    rw [← Scheme.Hom.comp_preimage]
    simpa [b, f₀] using (hW c.pt (c.π.app (op i))).mp hst
  obtain ⟨j, a, ha⟩ := exists_map_eq_top B b
    (isLimitBaseChangeCone D c U.hom hc) (f₀ ⁻¹ᵁ W) hlimit
  refine ⟨j.left.unop, j.hom.unop, (hW _ _).mpr ?_⟩
  rw [← Scheme.Hom.comp_preimage] at ha
  simpa [B, f₀] using ha

end AlgebraicGeometry.Etale

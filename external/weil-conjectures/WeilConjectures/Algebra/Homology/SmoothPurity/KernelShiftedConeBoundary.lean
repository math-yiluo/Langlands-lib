/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
public import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.Refinements
public import Mathlib.CategoryTheory.Abelian.Refinements

/-!
# The boundary of the kernel-to-mapping-fibre comparison

Source: Stacks Project, Derived Categories, section Cones and termwise split sequences;
Homology, lemma-long-exact-sequence-cochain (Tag 0117)
(blueprint: lem-pur-kernel-shifted-cone-boundary).
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace CochainComplex

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The shifted cone inclusion induces the connecting map of the kernel sequence.
Source: Stacks Project, Derived Categories, section Cones and termwise split sequences;
Homology, lemma-long-exact-sequence-cochain (Tag 0117)
(blueprint: lem-pur-kernel-shifted-cone-boundary).

Proof. Fix a cycle b of B in degree q-1 and lift it to a in A, using degreewise
surjectivity. Its differential da lies in the kernel and represents the connecting
class. In the cone shifted by -1, the differential of (a,0) is (da,-b).
Consequently the classes of (0,b) and (da,0) agree. The two component identities
for κ identify the latter with κ(da), proving the asserted equality on cycles.
Cycles surject onto homology, so this proves equality of the morphisms. Equivalently,
use an epimorphic refinement to lift a cycle and apply ShortExact.δ_eq; the argument
includes q=0 and unbounded complexes, with no boundedness assumption.
-/
theorem kernelShiftedCone_boundary
    {C : Type*} [Category* C] [Abelian C]
    {A B : CochainComplex C ℤ} (r : A ⟶ B)
    (hS : (ShortComplex.mk (kernel.ι r) r (kernel.condition r)).ShortExact)
    (κ : kernel r ⟶ (mappingCone r)⟦(-1 : ℤ)⟧)
    (hκ : ∀ n : ℤ,
      κ.f n ≫ ((mappingCone r).shiftFunctorObjXIso (-1) n (n - 1) (by omega)).hom ≫
        homotopyCofiber.sndX r (n - 1) = 0 ∧
      κ.f n ≫ ((mappingCone r).shiftFunctorObjXIso (-1) n (n - 1) (by omega)).hom ≫
        homotopyCofiber.fstX r (n - 1) n (by change n - 1 + 1 = n; omega) =
        (kernel.ι r).f n) (q : ℤ) :
    homologyMap ((CategoryTheory.shiftFunctor _ (-1 : ℤ)).map (mappingCone.inr r)) q =
      (ShiftSequence.shiftIso C (-1) q (q - 1) (by omega)).hom.app B ≫
        hS.δ (q - 1) q (by change q - 1 + 1 = q; omega) ≫ homologyMap κ q := by
  have : Epi r := hS.epi_g
  have (n : ℤ) : Epi (r.f n) := inferInstance
  apply yoneda.map_injective
  ext ⟨D⟩ (x : D ⟶ _)
  change x ≫ _ = x ≫ _
  obtain ⟨D₁, π₁, _, z, hz, hzx⟩ :=
    (B⟦(-1 : ℤ)⟧).eq_liftCycles_homologyπ_up_to_refinements x (q + 1) (by simp)
  let b := z ≫ (B.shiftFunctorObjXIso (-1) q (q - 1) (by omega)).hom
  obtain ⟨D₂, π₂, _, a, ha⟩ := surjective_up_to_refinements_of_epi (r.f (q - 1)) b
  have hb : b ≫ B.d (q - 1) q = 0 := by
    apply (cancel_mono
      (B.shiftFunctorObjXIso (-1) (q + 1) q (by omega)).inv).1
    simp only [b, shiftFunctorObjXIso, Category.assoc, XIsoOfEq_hom_comp_d,
      d_comp_XIsoOfEq_inv, zero_comp]
    simpa [shiftFunctor_obj_d', Linear.comp_units_smul] using hz
  have hc₀ : (a ≫ A.d (q - 1) q) ≫ r.f q = 0 := by
    rw [Category.assoc, ← r.comm, ← Category.assoc, ← ha, Category.assoc, hb, comp_zero]
  obtain ⟨c, hc⟩ := KernelFork.IsLimit.lift'
    ((hS.map (eval C (.up ℤ) q)).fIsKernel)
    (a ≫ A.d (q - 1) q) hc₀
  change c ≫ (kernel.ι r).f q = a ≫ A.d (q - 1) q at hc
  apply (cancel_epi π₁).1
  rw [reassoc_of% hzx, reassoc_of% hzx]
  apply (cancel_epi π₂).1
  simp only [HomologicalComplex.comp_liftCycles_assoc]
  rw [HomologicalComplex.homologyπ_naturality,
    HomologicalComplex.liftCycles_comp_cyclesMap_assoc]
  rw [B.liftCycles_shift_homologyπ_assoc (π₂ ≫ z) (q + 1) (by simp) _
    (q - 1) (by omega) q (by simp)]
  simp only [Category.assoc]
  change _ = B.liftCycles (π₂ ≫ b) q (by simp) _ ≫ B.homologyπ (q - 1) ≫
    (ShiftSequence.shiftIso C (-1) q (q - 1) (by omega)).inv.app B ≫
    (ShiftSequence.shiftIso C (-1) q (q - 1) (by omega)).hom.app B ≫
    hS.δ (q - 1) q (by change q - 1 + 1 = q; omega) ≫ homologyMap κ q
  rw [Iso.inv_hom_id_app_assoc]
  have hd := hS.δ_eq (q - 1) q (by change q - 1 + 1 = q; omega)
    (π₂ ≫ b) (by simp only [Category.assoc, hb, comp_zero]) a ha.symm c hc
    (q + 1) (by simp)
  rw [reassoc_of% hd]
  rw [HomologicalComplex.homologyπ_naturality,
    HomologicalComplex.liftCycles_comp_cyclesMap_assoc]
  apply ((mappingCone r)⟦(-1 : ℤ)⟧).liftCycles_comp_homologyπ_eq_iff_up_to_refinements
    (q - 1) q (q + 1) (by simp) (by simp) _ _ _ _ |>.2
  refine ⟨D₂, 𝟙 _, inferInstance,
    (-a) ≫ homotopyCofiber.inlX r (q - 1) (q - 2)
      (by change q - 2 + 1 = q - 1; omega) ≫
      ((mappingCone r).shiftFunctorObjXIso (-1) (q - 1) (q - 2) (by omega)).inv, ?_⟩
  simp only [Category.id_comp]
  apply (cancel_mono
    ((mappingCone r).shiftFunctorObjXIso (-1) q (q - 1) (by omega)).hom).1
  simp only [CategoryTheory.Preadditive.add_comp, Category.assoc]
  simp only [shiftFunctor_obj_d', shiftFunctorObjXIso, Linear.comp_units_smul,
    Linear.units_smul_comp, XIsoOfEq_inv_comp_d, d_comp_XIsoOfEq_hom]
  have hk := hκ q
  dsimp only [mappingCone] at hk ⊢
  simp only [shiftFunctorObjXIso, XIsoOfEq_rfl, Iso.refl_hom] at hk
  simp only [shiftFunctor_map_f', mappingCone.inr, homotopyCofiber.inr_f,
    XIsoOfEq_rfl, Iso.refl_hom,
    Int.negOnePow_neg, Int.negOnePow_one, Units.neg_smul, one_smul,
    CategoryTheory.Preadditive.neg_comp, neg_neg]
  apply homotopyCofiber.ext_to_X r (q - 1) q
    (by change q - 1 + 1 = q; omega)
  · simp only [CategoryTheory.Preadditive.add_comp, Category.assoc,
      hk.2]
    erw [Category.id_comp]
    simp only [homotopyCofiber_d, homotopyCofiber.d_fstX r
      (q - 2) (q - 1) q (by change q - 2 + 1 = q - 1; omega)
        (by change q - 1 + 1 = q; omega)]
    simp only [CategoryTheory.Preadditive.comp_neg, homotopyCofiber.inlX_fstX_assoc,
      hc, add_neg_cancel]
    erw [homotopyCofiber.inrX_fstX]
    simp only [comp_zero]
  · simp only [CategoryTheory.Preadditive.add_comp, Category.assoc,
      hk.1]
    erw [Category.id_comp]
    simp only [comp_zero, zero_add]
    simp only [homotopyCofiber_d, homotopyCofiber.d_sndX r
      (q - 2) (q - 1) (by change q - 2 + 1 = q - 1; omega)]
    simp only [CategoryTheory.Preadditive.comp_add,
      homotopyCofiber.inlX_fstX_assoc, homotopyCofiber.inlX_sndX_assoc,
      zero_comp, add_zero]
    erw [homotopyCofiber.inrX_sndX, Category.comp_id]
    have ha' := ha
    dsimp only [b, shiftFunctorObjXIso] at ha'
    erw [Category.comp_id] at ha'
    exact ha'

end CochainComplex

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle

/-!
# The split-row boundary on cocycles

Source: Stacks Project, Derived Categories, Tags 0152 and 06XR.
(blueprint: lem-sc-p1-split-ses-cocycle-boundary).
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits CochainComplex.HomComplex

namespace CochainComplex

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A lift followed by its differential computes composition with the split boundary.
Source: Stacks Project, Derived Categories, Tags 0152 and 06XR, the canonical
boundary and its computation by homotopy classes of maps into resolutions.
(blueprint: lem-sc-p1-split-ses-cocycle-boundary).

Proof: The split boundary has component sⁿ d₂ rⁿ⁺¹. Put t = b rⁿ. The splitting
identity gives b = t fⁿ + c sⁿ. Multiply by d₂ and use f d₂ = d₁ f. Since
b d₂ = a fⁿ⁺¹ and fⁿ⁺¹ rⁿ⁺¹ = id, obtain c sⁿ d₂ rⁿ⁺¹ = a - t d₁.
Thus the cocycle obtained by composing c with the degree-one split boundary differs
from a by the coboundary of t. The unsigned shift of fromSingleMk identifies
composition of these shifted maps with this component formula. The maps from the
single complex are consequently homotopic; Q identifies them. No injectivity,
boundedness, or augmentation is used, and n may be any integer. In the zero row the
same identities give zero on both sides. -/
theorem degreewiseSplit_cocycle_boundary
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (S : ShortComplex (CochainComplex C ℤ))
    (σ : ∀ k : ℤ,
      (S.map (HomologicalComplex.eval C (ComplexShape.up ℤ) k)).Splitting)
    (M : C) (n : ℤ) (c : M ⟶ S.X₃.X n)
    (hc : c ≫ S.X₃.d n (n + 1) = 0)
    (b : M ⟶ S.X₂.X n) (hb : b ≫ S.g.f n = c)
    (a : M ⟶ S.X₁.X (n + 1))
    (ha : a ≫ S.X₁.d (n + 1) (n + 1 + 1) = 0)
    (hba : b ≫ S.X₂.d n (n + 1) = a ≫ S.f.f (n + 1)) :
    (ShiftedHom.map (Cocycle.equivHomShift.symm
      (Cocycle.fromSingleMk c (zero_add n) (n + 1) rfl hc)) DerivedCategory.Q).comp
        (ShiftedHom.map (homOfDegreewiseSplit S σ) DerivedCategory.Q)
        (show (1 : ℤ) + n = n + 1 by omega) =
      ShiftedHom.map (Cocycle.equivHomShift.symm
        (Cocycle.fromSingleMk a (zero_add (n + 1)) (n + 1 + 1) rfl ha))
          DerivedCategory.Q := by
  dsimp only [ShortComplex.map, HomologicalComplex.eval] at σ
  let z := Cocycle.fromSingleMk c (zero_add n) (n + 1) rfl hc
  let y := Cocycle.fromSingleMk a (zero_add (n + 1)) (n + 1 + 1) rfl ha
  let φ := ShiftedHom.comp (Cocycle.equivHomShift.symm z) (homOfDegreewiseSplit S σ)
    (show (1 : ℤ) + n = n + 1 by omega)
  have hv : (Cocycle.equivHomShift φ).1.v 0 (n + 1) (zero_add _) =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).hom ≫
        c ≫ (σ n).s ≫ S.X₂.d n (n + 1) ≫ (σ (n + 1)).r := by
    simp only [ShiftedHom.comp, Cocycle.equivHomShift_symm_apply,
      Cocycle.equivHomShift_apply, Cocycle.rightUnshift_coe, Cocycle.ofHom_coe,
      Cochain.ofHom_comp, Cocycle.cochain_ofHom_homOf_eq_coe, Cocycle.rightShift_coe,
      Cocycle.fromSingleMk_coe, Cochain.rightUnshift_v _ _ _ _ _ _ _ (add_zero 0),
      shiftFunctor_obj_X', Cochain.comp_zero_cochain_v,
      Cochain.rightShift_v _ _ _ _ _ _ _ _ (zero_add n), shiftFunctor_obj_X,
      Cochain.fromSingleMk_v, shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq,
      eqToIso.inv, Category.assoc, Cochain.ofHom_v, shiftFunctor_map_f',
      homOfDegreewiseSplit_f, cocycleOfDegreewiseSplit, ShortComplex.map_X₂,
      HomologicalComplex.eval_obj, Cocycle.mk_coe, Cochain.mk_v,
      shiftFunctorAdd'_inv_app_f', eqToIso.hom, eqToHom_trans,
      Iso.cancel_iso_hom_left, φ, z]
    change c ≫ eqToHom (congrArg S.X₃.X (zero_add n).symm) ≫ (σ (0 + n)).s ≫
      S.X₂.d (0 + n) (0 + n + 1) ≫ (σ (0 + n + 1)).r ≫
        eqToHom (congrArg S.X₁.X (congrArg (fun k : ℤ ↦ k + 1) (zero_add n))) = _
    have ht (i j : ℤ) (h : i = j) :
        eqToHom (congrArg S.X₃.X h.symm) ≫ (σ i).s ≫ S.X₂.d i (i + 1) ≫
          (σ (i + 1)).r ≫
            eqToHom (congrArg S.X₁.X (congrArg (fun k : ℤ ↦ k + 1) h)) =
              (σ j).s ≫ S.X₂.d j (j + 1) ≫ (σ (j + 1)).r := by
      subst j
      simp
    simpa only [Category.assoc] using congrArg (fun f ↦ c ≫ f) (ht (0 + n) n (zero_add n))
  have hcomp : c ≫ (σ n).s ≫ S.X₂.d n (n + 1) ≫ (σ (n + 1)).r =
      a - (b ≫ (σ n).r) ≫ S.X₁.d n (n + 1) := by
    have hs := (σ n).g_s
    have hr := (σ (n + 1)).f_r
    dsimp at hs hr ⊢
    calc
      _ = b ≫ (S.g.f n ≫ (σ n).s) ≫ S.X₂.d n (n + 1) ≫ (σ (n + 1)).r := by
        simp only [← hb, Category.assoc]
      _ = b ≫ (𝟙 _ - (σ n).r ≫ S.f.f n) ≫
          S.X₂.d n (n + 1) ≫ (σ (n + 1)).r := by
        erw [hs]
      _ = _ := by
        dsimp at ⊢
        simp only [Preadditive.comp_sub, Preadditive.sub_comp, Category.id_comp,
          Category.assoc]
        erw [S.f.comm_assoc]
        simp only [Category.comp_id, reassoc_of% hba, hr]
  have hδ : δ n (n + 1) (Cochain.fromSingleMk (-(b ≫ (σ n).r)) (zero_add n)) =
      (Cocycle.equivHomShift φ - y).1 := by
    apply (Cochain.fromSingleEquiv (zero_add (n + 1))).injective
    rw [Cochain.δ_fromSingleMk _ _ _ (n + 1) (zero_add (n + 1)),
      Cochain.fromSingleEquiv_fromSingleMk]
    change (-b ≫ (σ n).r) ≫ S.X₁.d n (n + 1) =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).inv ≫
        (Cocycle.equivHomShift φ - y).1.v 0 (n + 1) (zero_add _)
    simp only [Cocycle.coe_sub, Cochain.sub_v, y, Cocycle.fromSingleMk_coe,
      Cochain.fromSingleMk_v, hv, hcomp, Preadditive.comp_sub, Category.assoc,
      Iso.inv_hom_id_assoc, Preadditive.neg_comp]
    abel
  have hd : Cocycle.equivHomShift φ - y ∈ coboundaries _ _ _ := by
    rw [mem_coboundaries_iff _ n rfl]
    exact ⟨Cochain.fromSingleMk (-(b ≫ (σ n).r)) (zero_add n), hδ⟩
  have hzero := (CohomologyClass.toHom_mk_eq_zero_iff
    (Cocycle.equivHomShift φ - y)).mpr hd
  have heq : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map φ =
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
        (Cocycle.equivHomShift.symm y) := by
    simpa only [CohomologyClass.toHom_mk, map_sub, Functor.map_sub,
      AddEquiv.symm_apply_apply, sub_eq_zero] using hzero
  rw [← ShiftedHom.map_comp]
  change ShiftedHom.map φ DerivedCategory.Q = ShiftedHom.map
    (Cocycle.equivHomShift.symm y) DerivedCategory.Q
  unfold ShiftedHom.map
  rw [DerivedCategory.Q_map_eq_of_homotopy C (HomotopyCategory.homotopyOfEq _ _ heq)]

end CochainComplex

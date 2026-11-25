/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.RingTheory.TensorProduct.Maps
public import WeilConjectures.AlgebraicGeometry.AffineBasePieceTensorBaseChangeInstance

/-!
# Affine base pieces of a base change

Given compatible spectrum models `Spec R`, `Spec B`, `Spec C` of an affine piece of the base
change of an `S`-morphism `f₀ : X₀ ⟶ Y₀` along `d : T ⟶ S`, and an affine chart `Spec A` of a
further test morphism `t : L ⟶ T`, the restriction of the base change of `f₀` along `t ≫ d` is
isomorphic as an arrow to `Spec (A ⊗[R] B) ⟶ Spec (A ⊗[R] C)` (Stacks, Tags 01JR, 01I4).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem composite_pullback_square
    {S T Z L : Scheme.{u}} (z : Z ⟶ S) (d : T ⟶ S) (t : L ⟶ T) :
    IsPullback
      ((pullbackLeftPullbackSndIso z d t).inv ≫
        pullback.fst (pullback.snd z d) t)
      (pullback.snd z (t ≫ d)) (pullback.snd z d) t := by
  refine IsPullback.of_iso_pullback ⟨?_⟩
    (pullbackLeftPullbackSndIso z d t).symm rfl ?_
  · simp [Category.assoc]
  · exact pullbackLeftPullbackSndIso_inv_snd_snd z d t

set_option backward.isDefEq.respectTransparency false in
/-- Restriction of a composite base change is the pullback of the restricted arrow,
when its target chart factors through the chosen base open.

Source: Stacks Project, Schemes, Tag 01JR (open fibre products). -/
theorem restricted_composite_base_change
    {S T : Scheme.{u}} (d : T ⟶ S)
    (X₀ Y₀ : Over S) (f₀ : X₀ ⟶ Y₀)
    (V : Y₀.left.Opens) (W : S.Opens)
    (q : ((pullback.fst Y₀.hom d) ⁻¹ᵁ V).toScheme ⟶ (d ⁻¹ᵁ W).toScheme)
    (hq : q ≫ (d ⁻¹ᵁ W).ι =
      ((pullback.fst Y₀.hom d) ⁻¹ᵁ V).ι ≫ pullback.snd Y₀.hom d)
    (L : Scheme.{u}) (t : L ⟶ T) :
    let g := (((Over.pullback d).map f₀).left) ∣_
      ((pullback.fst Y₀.hom d) ⁻¹ᵁ V)
    let s := t.resLE (d ⁻¹ᵁ W) _ le_rfl
    Nonempty
      (Arrow.mk ((((Over.pullback (t ≫ d)).map f₀).left) ∣_
        ((pullback.fst Y₀.hom (t ≫ d)) ⁻¹ᵁ V)) ≅
      Arrow.mk (pullback.map (g ≫ q) s q s g (𝟙 _) (𝟙 _)
        (by simp) (by simp))) := by
  dsimp only
  let fT := ((Over.pullback d).map f₀).left
  let fL := ((Over.pullback (t ≫ d)).map f₀).left
  let VB := (pullback.fst Y₀.hom d) ⁻¹ᵁ V
  let UC := fT ⁻¹ᵁ VB
  let VL := (pullback.fst Y₀.hom (t ≫ d)) ⁻¹ᵁ V
  let UL := fL ⁻¹ᵁ VL
  let WT := d ⁻¹ᵁ W
  let WL := t ⁻¹ᵁ WT
  let nY := (pullbackLeftPullbackSndIso Y₀.hom d t).inv ≫
    pullback.fst (pullback.snd Y₀.hom d) t
  let nX := (pullbackLeftPullbackSndIso X₀.hom d t).inv ≫
    pullback.fst (pullback.snd X₀.hom d) t
  have hnY₁ : nY ≫ pullback.fst Y₀.hom d =
      pullback.fst Y₀.hom (t ≫ d) := by simp [nY]
  have hnY₂ : nY ≫ pullback.snd Y₀.hom d =
      pullback.snd Y₀.hom (t ≫ d) ≫ t := by simp [nY]
  have hnX₁ : nX ≫ pullback.fst X₀.hom d =
      pullback.fst X₀.hom (t ≫ d) := by simp [nX]
  have hnX₂ : nX ≫ pullback.snd X₀.hom d =
      pullback.snd X₀.hom (t ≫ d) ≫ t := by simp [nX]
  have hfT₁ : fT ≫ pullback.fst Y₀.hom d =
      pullback.fst X₀.hom d ≫ f₀.left := by simp [fT, Over.pullback_map_left]
  have hfT₂ : fT ≫ pullback.snd Y₀.hom d =
      pullback.snd X₀.hom d := by simp [fT, Over.pullback_map_left]
  have hfL₁ : fL ≫ pullback.fst Y₀.hom (t ≫ d) =
      pullback.fst X₀.hom (t ≫ d) ≫ f₀.left := by simp [fL, Over.pullback_map_left]
  have hfL₂ : fL ≫ pullback.snd Y₀.hom (t ≫ d) =
      pullback.snd X₀.hom (t ≫ d) := by simp [fL, Over.pullback_map_left]
  have hn : nX ≫ fT = fL ≫ nY := by
    apply pullback.hom_ext
    · simp only [Category.assoc, hfT₁, hnY₁, reassoc_of% hnX₁, hfL₁]
    · simp only [Category.assoc, hfT₂, hnY₂,
        reassoc_of% hfL₂]
      exact hnX₂
  have eVB : VB ≤ (pullback.snd Y₀.hom d) ⁻¹ᵁ WT := by
    intro x hx
    have hh := congrArg (fun k ↦ k ⟨x, hx⟩) hq
    change (q ⟨x, hx⟩).val = pullback.snd Y₀.hom d x at hh
    change pullback.snd Y₀.hom d x ∈ WT
    rw [← hh]
    exact (q ⟨x, hx⟩).property
  have eUC : UC ≤ (pullback.snd X₀.hom d) ⁻¹ᵁ WT := by
    rw [← hfT₂, Scheme.Hom.comp_preimage]
    exact fT.preimage_mono eVB
  have hVL : VL = nY ⁻¹ᵁ VB := by
    dsimp [VL, VB]
    rw [← Scheme.Hom.comp_preimage, hnY₁]
  have hUL : UL = nX ⁻¹ᵁ UC := by
    change fL ⁻¹ᵁ VL = nX ⁻¹ᵁ (fT ⁻¹ᵁ VB)
    rw [hVL]
    exact (congrArg (fun k ↦ k ⁻¹ᵁ VB) hn).symm
  have eVL : VL ≤ (pullback.snd Y₀.hom (t ≫ d)) ⁻¹ᵁ WL := by
    rw [hVL]
    change nY ⁻¹ᵁ VB ≤ (pullback.snd Y₀.hom (t ≫ d)) ⁻¹ᵁ (t ⁻¹ᵁ WT)
    have hh := congrArg (fun k ↦ k ⁻¹ᵁ WT) hnY₂
    have hh' : nY ⁻¹ᵁ ((pullback.snd Y₀.hom d) ⁻¹ᵁ WT) =
        (pullback.snd Y₀.hom (t ≫ d)) ⁻¹ᵁ (t ⁻¹ᵁ WT) := by
      simpa only [Scheme.Hom.comp_preimage] using hh
    exact (nY.preimage_mono eVB).trans_eq hh'
  have eUL : UL ≤ (pullback.snd X₀.hom (t ≫ d)) ⁻¹ᵁ WL := by
    rw [hUL]
    change nX ⁻¹ᵁ UC ≤ (pullback.snd X₀.hom (t ≫ d)) ⁻¹ᵁ (t ⁻¹ᵁ WT)
    have hh := congrArg (fun k ↦ k ⁻¹ᵁ WT) hnX₂
    have hh' : nX ⁻¹ᵁ ((pullback.snd X₀.hom d) ⁻¹ᵁ WT) =
        (pullback.snd X₀.hom (t ≫ d)) ⁻¹ᵁ (t ⁻¹ᵁ WT) := by
      simpa only [Scheme.Hom.comp_preimage] using hh
    exact (nX.preimage_mono eUC).trans_eq hh'
  have hq' : (pullback.snd Y₀.hom d).resLE WT VB eVB = q := by
    rw [← cancel_mono WT.ι]
    exact (Scheme.Hom.resLE_comp_ι _ _).trans hq.symm
  have hqc : (pullback.snd X₀.hom d).resLE WT UC eUC = (fT ∣_ VB) ≫ q := by
    rw [← cancel_mono WT.ι]
    simp only [Scheme.Hom.resLE_comp_ι, Category.assoc]
    rw [show q ≫ WT.ι = VB.ι ≫ pullback.snd Y₀.hom d from hq,
      morphismRestrict_ι_assoc, hfT₂]
  have hB := Scheme.Hom.isPullback_resLE
    (composite_pullback_square Y₀.hom d t) (le_rfl : WL ≤ t ⁻¹ᵁ WT) eVB
    (UY := VL) (by rw [← hVL, inf_eq_left.mpr eVL])
  have hC := Scheme.Hom.isPullback_resLE
    (composite_pullback_square X₀.hom d t) (le_rfl : WL ≤ t ⁻¹ᵁ WT) eUC
    (UY := UL) (by rw [← hUL, inf_eq_left.mpr eUL])
  rw [hq'] at hB
  rw [hqc] at hC
  have hRT : (fT ∣_ VB) ≫ VB.ι = UC.ι ≫ fT := morphismRestrict_ι fT VB
  have hRL : (fL ∣_ VL) ≫ VL.ι = UL.ι ≫ fL := morphismRestrict_ι fL VL
  refine ⟨Arrow.isoMk hC.isoPullback hB.isoPullback ?_⟩
  dsimp only [Arrow.mk_hom]
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst]
    rw [reassoc_of% hC.isoPullback_hom_fst, hB.isoPullback_hom_fst]
    rw [← cancel_mono VB.ι]
    simp only [Category.assoc]
    rw [hRT, Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι_assoc,
      reassoc_of% hRL]
    simpa only [nX, nY, Category.assoc] using congrArg (fun k ↦ UL.ι ≫ k) hn
  · simp only [Category.assoc, pullback.lift_snd, Category.comp_id]
    rw [hC.isoPullback_hom_snd, hB.isoPullback_hom_snd]
    rw [← cancel_mono WL.ι]
    simp only [Category.assoc, Scheme.Hom.resLE_comp_ι]
    rw [reassoc_of% hRL, hfL₂]

open scoped TensorProduct in
private theorem tensor_pullback_arrow
    {H P Q M : Scheme.{u}} (g : P ⟶ Q) (q : Q ⟶ H) (s : M ⟶ H)
    (R A B C : CommRingCat.{u}) [Algebra R A] [Algebra R B] [Algebra R C]
    (φ : B →ₐ[R] C) (e0 : H ≅ Spec R) (eB : Q ≅ Spec B)
    (eC : P ≅ Spec C) (eA : M ≅ Spec A)
    (hB : q ≫ e0.hom = eB.hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap R B)))
    (hC : g ≫ eB.hom = eC.hom ≫ Spec.map (CommRingCat.ofHom φ.toRingHom))
    (hA : s ≫ e0.hom = eA.hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap R A))) :
    Nonempty (Arrow.mk (pullback.map (g ≫ q) s q s g (𝟙 _) (𝟙 _)
      (by simp) (by simp)) ≅ Arrow.mk (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map (AlgHom.id R A) φ).toRingHom))) := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap R B))
  let c := Spec.map (CommRingCat.ofHom (algebraMap R C))
  let a := Spec.map (CommRingCat.ofHom (algebraMap R A))
  have hc : (g ≫ q) ≫ e0.hom = eC.hom ≫ c := by
    rw [Category.assoc, hB, ← Category.assoc, hC, Category.assoc]
    dsimp [c]
    rw [← Spec.map_comp]
    congr 1
    exact congrArg (fun k : R →+* C ↦ Spec.map (CommRingCat.ofHom k)) φ.comp_algebraMap
  have hB' : b ≫ e0.inv = eB.inv ≫ q := by
    simpa [Category.assoc, b] using
      congrArg (fun k ↦ eB.inv ≫ k ≫ e0.inv) hB.symm
  have hC' : c ≫ e0.inv = eC.inv ≫ (g ≫ q) := by
    simpa [Category.assoc] using
      congrArg (fun k ↦ eC.inv ≫ k ≫ e0.inv) hc.symm
  have hA' : a ≫ e0.inv = eA.inv ≫ s := by
    simpa [Category.assoc, a] using
      congrArg (fun k ↦ eA.inv ≫ k ≫ e0.inv) hA.symm
  let jB : pullback q s ≅ pullback b a :=
    { hom := pullback.map q s b a eB.hom eA.hom e0.hom hB hA
      inv := pullback.map b a q s eB.inv eA.inv e0.inv hB' hA'
      hom_inv_id := by ext <;> simp
      inv_hom_id := by ext <;> simp }
  let jC : pullback (g ≫ q) s ≅ pullback c a :=
    { hom := pullback.map (g ≫ q) s c a eC.hom eA.hom e0.hom hc hA
      inv := pullback.map c a (g ≫ q) s eC.inv eA.inv e0.inv hC' hA'
      hom_inv_id := by ext <;> simp
      inv_hom_id := by ext <;> simp }
  let iB := jB ≪≫ pullbackSymmetry b a ≪≫ pullbackSpecIso R A B
  let iC := jC ≪≫ pullbackSymmetry c a ≪≫ pullbackSpecIso R A C
  have hb₁ : iB.inv ≫ pullback.fst q s =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom) ≫
        eB.inv := by
    dsimp [iB]
    simp only [Category.assoc]
    rw [← cancel_mono eB.hom]
    simp [jB, a, b, Category.assoc]
  have hb₂ : iB.inv ≫ pullback.snd q s =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] B)) ≫
        eA.inv := by
    dsimp [iB]
    simp only [Category.assoc]
    rw [← cancel_mono eA.hom]
    simp [jB, a, b, Category.assoc]
  have hc₁ : iC.inv ≫ pullback.fst (g ≫ q) s =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : C →ₐ[R] A ⊗[R] C).toRingHom) ≫
        eC.inv := by
    dsimp [iC]
    simp only [Category.assoc]
    rw [← cancel_mono eC.hom]
    simp [jC, a, c, Category.assoc]
  have hc₂ : iC.inv ≫ pullback.snd (g ≫ q) s =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] C)) ≫
        eA.inv := by
    dsimp [iC]
    simp only [Category.assoc]
    rw [← cancel_mono eA.hom]
    simp [jC, a, c, Category.assoc]
  let ψ := Algebra.TensorProduct.map (AlgHom.id R A) φ
  let sψ := Spec.map (CommRingCat.ofHom ψ.toRingHom)
  have hRight : sψ ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom) =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : C →ₐ[R] A ⊗[R] C).toRingHom) ≫
        Spec.map (CommRingCat.ofHom φ.toRingHom) := by
    dsimp [sψ]
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
  have hLeft : sψ ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] B)) =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] C)) := by
    dsimp [sψ]
    rw [← Spec.map_comp]
    congr 1
    ext x
    simp [ψ]
  have hh : sψ ≫ iB.inv = iC.inv ≫
      pullback.map (g ≫ q) s q s g (𝟙 _) (𝟙 _) (by simp) (by simp) := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst]
      rw [hb₁, reassoc_of% hRight, reassoc_of% hc₁]
      rw [← cancel_mono eB.hom]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rw [hC, Iso.inv_hom_id_assoc]
    · simp only [Category.assoc, pullback.lift_snd, Category.comp_id]
      rw [hb₂, ← Category.assoc, hLeft, hc₂]
  refine ⟨Arrow.isoMk' _ sψ iC iB ?_⟩
  rw [← cancel_epi iC.inv, ← cancel_mono iB.inv]
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id,
    Category.comp_id] using hh

end AlgebraicGeometry

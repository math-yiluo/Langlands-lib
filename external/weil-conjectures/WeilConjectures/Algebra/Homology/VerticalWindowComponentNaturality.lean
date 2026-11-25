/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.VerticalWindowComponentIso

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]

set_option backward.isDefEq.respectTransparency false in
private lemma lower_opcycles_naturality
    {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
    {D : Type*} [Category D] [Abelian D]
    {A B : HomologicalComplex D c'} (g : A ⟶ B)
    (e : c.Embedding c') [e.IsTruncGE]
    {i : ι} {i' : ι'} (h : e.f i = i') (hi : e.BoundaryGE i) :
    (A.truncGEXIsoOpcycles e h hi).inv ≫ (HomologicalComplex.truncGEMap g e).f i' =
      HomologicalComplex.opcyclesMap g i' ≫ (B.truncGEXIsoOpcycles e h hi).inv := by
  simp only [HomologicalComplex.truncGEXIsoOpcycles, Iso.trans_inv,
    HomologicalComplex.truncGEMap, ComplexShape.Embedding.extendFunctor_map]
  rw [HomologicalComplex.extendMap_f _ e h,
    HomologicalComplex.truncGE'Map_f_eq_opcyclesMap _ e hi h]
  simp

set_option backward.isDefEq.respectTransparency false in
private lemma upper_cycles_naturality {A B : CochainComplex C ℤ} (g : A ⟶ B)
    (n : ℤ) :
    (CochainComplex.truncLEMap g n).f n ≫
        (CochainComplex.truncLEXIsoCycles B n).hom =
      (CochainComplex.truncLEXIsoCycles A n).hom ≫
        HomologicalComplex.cyclesMap g n := by
  let e := ComplexShape.embeddingUpIntLE n
  have h : e.op.f 0 = n := by simp [e]
  have hi : e.op.BoundaryGE 0 := by
    change e.BoundaryLE 0
    simp [e, ComplexShape.boundaryLE_embeddingUpIntLE_iff]
  apply Quiver.Hom.op_inj
  change ((B.opcyclesOpIso n).inv ≫ (B.op.truncGEXIsoOpcycles e.op h hi).inv) ≫
      (HomologicalComplex.truncGEMap
        ((HomologicalComplex.opFunctor C (ComplexShape.up ℤ)).map g.op) e.op).f n =
    (HomologicalComplex.cyclesMap g n).op ≫ (A.opcyclesOpIso n).inv ≫
      (A.op.truncGEXIsoOpcycles e.op h hi).inv
  rw [Category.assoc, lower_opcycles_naturality, ← Category.assoc,
    ← HomologicalComplex.opcyclesOpIso_inv_naturality, Category.assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
private lemma lower_homology_inv_naturality {A B : CochainComplex C ℤ}
    (g : A ⟶ B) (n : ℤ) :
    HomologicalComplex.homologyMap (CochainComplex.truncGEMap g n) n ≫
        inv (HomologicalComplex.homologyMap (CochainComplex.πTruncGE B n) n) =
      inv (HomologicalComplex.homologyMap (CochainComplex.πTruncGE A n) n) ≫
        HomologicalComplex.homologyMap g n := by
  have h := congrArg (fun k ↦ HomologicalComplex.homologyMap k n)
    (CochainComplex.πTruncGE_naturality g n)
  simp only [HomologicalComplex.homologyMap_comp] at h
  rw [← cancel_epi (HomologicalComplex.homologyMap (CochainComplex.πTruncGE A n) n)]
  simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  rw [h]
  simp

set_option backward.isDefEq.respectTransparency false in
private lemma truncation_comparison_naturality {A B : CochainComplex C ℤ}
    (g : A ⟶ B) (n : ℤ) :
    (CochainComplex.truncLEMap (CochainComplex.truncGEMap g n) n).f n ≫
        (CochainComplex.truncLEXIsoCycles (CochainComplex.truncGE B n) n).hom ≫
        (CochainComplex.truncGE B n).homologyπ n ≫
        inv (HomologicalComplex.homologyMap (CochainComplex.πTruncGE B n) n) =
      (CochainComplex.truncLEXIsoCycles (CochainComplex.truncGE A n) n).hom ≫
        (CochainComplex.truncGE A n).homologyπ n ≫
        inv (HomologicalComplex.homologyMap (CochainComplex.πTruncGE A n) n) ≫
        HomologicalComplex.homologyMap g n := by
  rw [← Category.assoc, upper_cycles_naturality]
  simp only [Category.assoc]
  rw [← HomologicalComplex.homologyπ_naturality_assoc]
  rw [lower_homology_inv_naturality]

set_option backward.isDefEq.respectTransparency false in
private lemma extension_window_naturality (q : ℕ)
    {K L : CochainComplex C ℕ} (f : K ⟶ L) :
    (CochainComplex.truncLEMap
      (CochainComplex.truncGEMap
        (HomologicalComplex.extendMap f ComplexShape.embeddingUpNat) (q : ℤ))
      (q : ℤ)).f (q : ℤ) ≫
        (CochainComplex.truncLEXIsoCycles
          (CochainComplex.truncGE (L.extend ComplexShape.embeddingUpNat) (q : ℤ))
          (q : ℤ)).hom ≫
        (CochainComplex.truncGE (L.extend ComplexShape.embeddingUpNat) (q : ℤ)).homologyπ
          (q : ℤ) ≫
        inv (HomologicalComplex.homologyMap
          (CochainComplex.πTruncGE (L.extend ComplexShape.embeddingUpNat) (q : ℤ))
          (q : ℤ)) ≫
        (L.extendHomologyIso ComplexShape.embeddingUpNat (by rfl)).hom =
      (CochainComplex.truncLEXIsoCycles
          (CochainComplex.truncGE (K.extend ComplexShape.embeddingUpNat) (q : ℤ))
          (q : ℤ)).hom ≫
        (CochainComplex.truncGE (K.extend ComplexShape.embeddingUpNat) (q : ℤ)).homologyπ
          (q : ℤ) ≫
        inv (HomologicalComplex.homologyMap
          (CochainComplex.πTruncGE (K.extend ComplexShape.embeddingUpNat) (q : ℤ))
          (q : ℤ)) ≫
        (K.extendHomologyIso ComplexShape.embeddingUpNat (by rfl)).hom ≫
        HomologicalComplex.homologyMap f q := by
  let e := ComplexShape.embeddingUpNat
  let g := HomologicalComplex.extendMap f e
  have h := truncation_comparison_naturality g (q : ℤ)
  have h' := congrArg (fun k ↦ k ≫ (L.extendHomologyIso e (by rfl)).hom) h
  dsimp only [g] at h'
  simp only [Category.assoc] at h'
  rw [HomologicalComplex.extendHomologyIso_hom_naturality f e (by rfl)] at h'
  exact h'

private lemma transport_naturality {D : Type*} [Category D] {ι : Type*} {i j : ι} (h : i = j)
    (A B : ι → D) (g : ∀ n, A n ⟶ B n) {X Y : D}
    (a : A j ≅ X) (b : B j ≅ Y) (f : X ⟶ Y)
    (hg : g j ≫ b.hom = a.hom ≫ f) :
    g i ≫ (cast (congrArg (fun n ↦ B n ≅ Y) h.symm) b).hom =
      (cast (congrArg (fun n ↦ A n ≅ X) h.symm) a).hom ≫ f := by
  cases h
  exact hg

set_option backward.isDefEq.respectTransparency false in
/-- The canonical component identifications commute with maps of complexes.
Source: blueprint thm-sp-double-complex-spectral-sequences, proof step 2.
Proof: away from q both sides are maps from zero objects. At q, the upper
truncation cycles comparison commutes with cyclesMap, homologyπ commutes with
homologyMap, the inverse homology map of the lower truncation projection is
natural by naturality of that projection, and the extension homology comparison
is natural. Composing these four squares gives the required degree-q square.
(blueprint: lem-sp-vertical-window-component-naturality). -/
theorem verticalWindow_component_naturality (q : ℕ)
    {K L : CochainComplex C ℕ} (f : K ⟶ L) :
    (verticalWindow (C := C) (q : ℤ) (q + 1)).map f ≫
        (verticalWindowComponentIso q L).hom =
      (verticalWindowComponentIso q K).hom ≫
        (HomologicalComplex.single C (ComplexShape.up ℕ) q).map
          (HomologicalComplex.homologyMap f q) := by
  have hd :
      ((verticalWindow (C := C) (q : ℤ) (q + 1)).map f).f q ≫
          (verticalWindowDegreeIso q L).hom =
        (verticalWindowDegreeIso q K).hom ≫
          HomologicalComplex.homologyMap f q := by
    let E (M : CochainComplex C ℕ) := M.extend ComplexShape.embeddingUpNat
    let T (M : CochainComplex C ℕ) := CochainComplex.truncGE (E M) (q : ℤ)
    have hπ (M : CochainComplex C ℕ) :
        IsIso (HomologicalComplex.homologyMap (CochainComplex.πTruncGE (E M) (q : ℤ))
          (q : ℤ)) := by infer_instance
    let e (M : CochainComplex C ℕ) :=
      CochainComplex.truncLEXIsoCycles (T M) (q : ℤ) ≪≫
        (T M).isoHomologyπ (q - 1) q (by simp)
          ((CochainComplex.isZero_of_isStrictlyGE (T M) (q : ℤ) (q - 1)
            (by omega)).eq_of_src _ _) ≪≫
        (asIso (HomologicalComplex.homologyMap
          (CochainComplex.πTruncGE (E M) (q : ℤ)) (q : ℤ))).symm ≪≫
        M.extendHomologyIso ComplexShape.embeddingUpNat (by rfl)
    have hn := transport_naturality (D := C) (add_sub_cancel_right (q : ℤ) 1)
      (fun n ↦ (CochainComplex.truncLE (T K) n).X (q : ℤ))
      (fun n ↦ (CochainComplex.truncLE (T L) n).X (q : ℤ))
      (fun n ↦ (CochainComplex.truncLEMap
        (CochainComplex.truncGEMap
          (HomologicalComplex.extendMap f ComplexShape.embeddingUpNat) (q : ℤ)) n).f
        (q : ℤ)) (e K) (e L) (HomologicalComplex.homologyMap f q)
      (by simpa [e, E, T, Category.assoc] using extension_window_naturality (C := C) q f)
    exact hn
  apply HomologicalComplex.to_single_hom_ext
  simpa [verticalWindowComponentIso, HomologicalComplex.single_map_f_self,
    Category.assoc] using congrArg
      (fun k ↦ k ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) q
        (L.homology q)).inv) hd

end HomologicalComplex₂

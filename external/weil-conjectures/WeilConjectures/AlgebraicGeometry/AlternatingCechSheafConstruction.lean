/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AlternatingCechTotalComplex
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
public import Mathlib.CategoryTheory.Adjunction.Additive

/-! # Explicit increasing-tuple complexes of module sheaves

Source: Stacks Project, Tag 01FM, alternating face maps.
(blueprint: def-pc-s3-alternating-cech-sheaf-construction).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry
noncomputable section

variable {X : Scheme.{u}}

/-- Intersection with a fixed open, as a functor on opens. Source: Stacks 01FM
(blueprint: def-pc-s3-alternating-cech-sheaf-construction). -/
def cechCapFunctor (W : X.Opens) : X.Opens ⥤ X.Opens where
  obj V := V ⊓ W
  map h := homOfLE (inf_le_inf_right W (leOfHom h))

/-- Restriction of rings to intersections. Source: Stacks 01FM
(blueprint: def-pc-s3-alternating-cech-sheaf-construction). -/
def cechCapRingMap (W : X.Opens) :
    X.ringCatSheaf.obj ⟶ (cechCapFunctor W).op ⋙ X.ringCatSheaf.obj where
  app V := X.ringCatSheaf.obj.map (homOfLE (inf_le_left : V.unop ⊓ W ≤ V.unop)).op
  naturality := by
    intro V Z h
    simp only [Functor.comp_map, ← Functor.map_comp]
    rfl

/-- The module presheaf with sections G(V ∩ W), scalars restricted from V.
Source: Stacks 01FM (blueprint: def-pc-s3-alternating-cech-sheaf-construction). -/
def cechCapModule (G : X.Modules) (W : X.Opens) :
    PresheafOfModules.{u} X.ringCatSheaf.obj :=
  (PresheafOfModules.pushforward (cechCapRingMap W)).obj G.val

/-- Restriction between intersection presheaves. Source: Stacks 01FM
(blueprint: def-pc-s3-alternating-cech-sheaf-construction). -/
def cechCapModuleMap (G : X.Modules) {W Z : X.Opens} (h : W ≤ Z) :
    cechCapModule G Z ⟶ cechCapModule G W where
  app V := ModuleCat.ofHom
    (X := (cechCapModule G Z).obj V) (Y := (cechCapModule G W).obj V)
    { toFun := fun s ↦ G.val.map (homOfLE (inf_le_inf_left V.unop h)).op s
      map_add' := by intros; simp
      map_smul' := by
        intro a s
        change G.val.map (homOfLE (inf_le_inf_left V.unop h)).op
            ((X.ringCatSheaf.obj.map
              (homOfLE (inf_le_left : V.unop ⊓ Z ≤ V.unop)).op a) •
                (show G.val.obj (op (V.unop ⊓ Z)) from s)) =
          (X.ringCatSheaf.obj.map
            (homOfLE (inf_le_left : V.unop ⊓ W ≤ V.unop)).op a) •
            G.val.map (homOfLE (inf_le_inf_left V.unop h)).op s
        rw [PresheafOfModules.map_smul]
        congr 1
        rw [← RingCat.comp_apply, ← Functor.map_comp]
        rfl }
  naturality := by
    intro V T a
    ext s
    change G.val.map (homOfLE (inf_le_inf_left T.unop h)).op
        (G.val.map (homOfLE (inf_le_inf_right Z (leOfHom a.unop))).op s) =
      G.val.map (homOfLE (inf_le_inf_right W (leOfHom a.unop))).op
        (G.val.map (homOfLE (inf_le_inf_left V.unop h)).op s)
    rw [← PresheafOfModules.map_comp_apply, ← PresheafOfModules.map_comp_apply]
    rfl

private theorem cechCapModuleMap_comp (G : X.Modules) {V W Z : X.Opens}
    (h : V ≤ W) (h' : W ≤ Z) :
    cechCapModuleMap G h' ≫ cechCapModuleMap G h = cechCapModuleMap G (h.trans h') := by
  ext A s
  change G.val.map (homOfLE (inf_le_inf_left A.unop h)).op
      (G.val.map (homOfLE (inf_le_inf_left A.unop h')).op s) =
    G.val.map (homOfLE (inf_le_inf_left A.unop (h.trans h'))).op s
  rw [← PresheafOfModules.map_comp_apply]
  rfl

/-- The degree-p module presheaf, a finite product over increasing tuples.
Source: Stacks 01FM (blueprint: def-pc-s3-alternating-cech-sheaf-construction). -/
def alternatingCechSheafPresheafTerms {r : ℕ} (U : Fin r → X.Opens) (G : X.Modules)
    (p : ℕ) : PresheafOfModules.{u} X.ringCatSheaf.obj :=
  ∏ᶜ fun t : Fin (p + 1) ↪o Fin r ↦ cechCapModule G (alternatingCechIntersection U t)

/-- The alternating differential on intersection module presheaves.
Source: Stacks 01FM (blueprint: def-pc-s3-alternating-cech-sheaf-construction). -/
def alternatingCechSheafPresheafD {r : ℕ} (U : Fin r → X.Opens) (G : X.Modules)
    (p : ℕ) : alternatingCechSheafPresheafTerms U G p ⟶
      alternatingCechSheafPresheafTerms U G (p + 1) :=
  Pi.lift fun t ↦ ∑ j : Fin (p + 2), (-1 : ℤ) ^ j.val •
    (Pi.π _ ((Fin.succAboveOrderEmb j).trans t) ≫
      cechCapModuleMap G (alternatingCechIntersection_face_le U p t j))

private theorem alternatingCechSheafPresheafD_π {r : ℕ} (U : Fin r → X.Opens)
    (G : X.Modules) (p : ℕ) (t : Fin (p + 2) ↪o Fin r) :
    alternatingCechSheafPresheafD U G p ≫ Pi.π _ t =
      ∑ j : Fin (p + 2), (-1 : ℤ) ^ j.val •
        (Pi.π _ ((Fin.succAboveOrderEmb j).trans t) ≫
          cechCapModuleMap G (alternatingCechIntersection_face_le U p t j)) := by
  simp only [alternatingCechSheafPresheafD, Pi.lift_comp_π]

/-- Signed face restrictions square to zero by pairing the two deletion orders.
Source: Stacks 01FM (blueprint: def-pc-s3-alternating-cech-sheaf-construction). -/
theorem alternatingCechSheafPresheafD_square {r : ℕ} (U : Fin r → X.Opens)
    (G : X.Modules) (p : ℕ) :
    alternatingCechSheafPresheafD U G p ≫
      alternatingCechSheafPresheafD U G (p + 1) = 0 := by
  classical
  apply Pi.hom_ext
  intro t
  rw [Category.assoc, alternatingCechSheafPresheafD_π]
  simp only [Preadditive.comp_sum, Preadditive.comp_zsmul, ← Category.assoc,
    alternatingCechSheafPresheafD_π, Preadditive.sum_comp, Preadditive.zsmul_comp,
    Finset.smul_sum, smul_smul, Limits.zero_comp]
  simp only [Category.assoc, cechCapModuleMap_comp]
  rw [Finset.sum_comm, ← Finset.sum_product', Finset.univ_product_univ]
  let P := Fin (p + 2) × Fin (p + 3)
  let S : Finset P := {ij : P | ij.2.val ≤ ij.1.val}
  rw [← Finset.sum_add_sum_compl S, ← eq_neg_iff_add_eq_zero,
    ← Finset.sum_neg_distrib]
  let φ : ∀ ij : P, ij ∈ S → P := fun ij hij ↦
    (Fin.castLT ij.2 (lt_of_le_of_lt (Finset.mem_filter.mp hij).right (Fin.is_lt ij.1)),
      ij.1.succ)
  apply Finset.sum_bij φ
  · intro ij hij
    simp only [S, φ, Finset.compl_filter, Finset.mem_filter_univ,
      Fin.val_succ, Fin.val_castLT] at hij ⊢
    omega
  · rintro ⟨i, j⟩ hij ⟨i', j'⟩ hij' h
    rw [Prod.mk_inj]
    exact ⟨by simpa [φ] using congrArg Prod.snd h,
      by simpa [φ, Fin.castSucc_castLT] using
        congrArg Fin.castSucc (congrArg Prod.fst h)⟩
  · rintro ⟨i', j'⟩ hij'
    simp only [S, Finset.compl_filter, Finset.mem_filter_univ, not_le] at hij'
    refine ⟨(j'.pred (by intro h; subst h; simp at hij'), i'.castSucc), ?_, ?_⟩
    · simpa [S] using Nat.le_sub_one_of_lt hij'
    · simp only [φ, Fin.castLT_castSucc, Fin.succ_pred]
  · rintro ⟨i, j⟩ hij
    dsimp only [φ]
    rw [← neg_smul]
    have hj : j ≤ i.castSucc := (Finset.mem_filter.mp hij).2
    have hpred : i.predAbove j = j.castLT (lt_of_le_of_lt hj i.is_lt) := by
      rw [Fin.predAbove_of_le_castSucc _ _ hj]
      rfl
    have hsucc : j.succAbove i = i.succ := Fin.succAbove_of_le_castSucc j i hj
    have ht : (Fin.succAboveOrderEmb i).trans ((Fin.succAboveOrderEmb j).trans t) =
        (Fin.succAboveOrderEmb (j.castLT (lt_of_le_of_lt hj i.is_lt))).trans
          ((Fin.succAboveOrderEmb i.succ).trans t) := by
      apply DFunLike.ext
      intro k
      apply congrArg t
      exact (hsucc ▸ hpred ▸
        (Fin.succAbove_succAbove_succAbove_predAbove j i k)).symm
    congr 1
    · simp only [Fin.val_succ, Fin.val_castLT, pow_succ, mul_neg, neg_mul, neg_neg, mul_one]
      exact mul_comm _ _
    · have hrestriction (a b : Fin (p + 1) ↪o Fin r)
          (ha : alternatingCechIntersection U t ≤ alternatingCechIntersection U a)
          (hb : alternatingCechIntersection U t ≤ alternatingCechIntersection U b)
          (hab : a = b) :
          Pi.π (fun q : Fin (p + 1) ↪o Fin r ↦
            cechCapModule G (alternatingCechIntersection U q)) a ≫
            cechCapModuleMap G ha =
          Pi.π (fun q : Fin (p + 1) ↪o Fin r ↦
            cechCapModule G (alternatingCechIntersection U q)) b ≫
            cechCapModuleMap G hb := by
        subst b
        rfl
      exact hrestriction _ _ _ _ ht

/-- The explicit nonnegative alternating complex of module presheaves.
Source: Stacks 01FM (blueprint: def-pc-s3-alternating-cech-sheaf-construction). -/
def alternatingCechSheafPresheafComplex {r : ℕ} (U : Fin r → X.Opens) (G : X.Modules) :
    CochainComplex (PresheafOfModules.{u} X.ringCatSheaf.obj) ℕ :=
  CochainComplex.of (alternatingCechSheafPresheafTerms U G)
    (alternatingCechSheafPresheafD U G) (alternatingCechSheafPresheafD_square U G)

/-- Restriction from G into the intersection presheaf. Source: Stacks 01FM
(blueprint: def-pc-s3-alternating-cech-sheaf-construction). -/
def cechCapModuleUnit (G : X.Modules) (W : X.Opens) : G.val ⟶ cechCapModule G W where
  app V := ModuleCat.ofHom (X := G.val.obj V) (Y := (cechCapModule G W).obj V)
    { toFun := fun s ↦ G.val.map (homOfLE (inf_le_left : V.unop ⊓ W ≤ V.unop)).op s
      map_add' := by intros; simp
      map_smul' := by intro a s; exact G.val.map_smul _ a s }
  naturality := by
    intro V Z h
    ext s
    change G.val.map (homOfLE (inf_le_left : Z.unop ⊓ W ≤ Z.unop)).op
        (G.val.map h s) =
      G.val.map (homOfLE (inf_le_inf_right W (leOfHom h.unop))).op
        (G.val.map (homOfLE (inf_le_left : V.unop ⊓ W ≤ V.unop)).op s)
    rw [← PresheafOfModules.map_comp_apply, ← PresheafOfModules.map_comp_apply]
    rfl

private theorem cechCapModuleUnit_comp (G : X.Modules) {W Z : X.Opens} (h : W ≤ Z) :
    cechCapModuleUnit G Z ≫ cechCapModuleMap G h = cechCapModuleUnit G W := by
  ext V s
  change G.val.map (homOfLE (inf_le_inf_left V.unop h)).op
      (G.val.map (homOfLE (inf_le_left : V.unop ⊓ Z ≤ V.unop)).op s) =
    G.val.map (homOfLE (inf_le_left : V.unop ⊓ W ≤ V.unop)).op s
  rw [← PresheafOfModules.map_comp_apply]
  rfl

/-- Degree-zero restriction augmentation. Source: Stacks 01FM
(blueprint: def-pc-s3-alternating-cech-sheaf-construction). -/
def alternatingCechSheafPresheafZero {r : ℕ} (U : Fin r → X.Opens) (G : X.Modules) :
    G.val ⟶ alternatingCechSheafPresheafTerms U G 0 :=
  Pi.lift fun t ↦ cechCapModuleUnit G (alternatingCechIntersection U t)

/-- The augmentation has zero composite with the first differential.
Source: Stacks 01FM (blueprint: def-pc-s3-alternating-cech-sheaf-construction).
Proof: the two face restrictions both restrict to the pair intersection and cancel. -/
theorem alternatingCechSheafPresheafZero_comp {r : ℕ} (U : Fin r → X.Opens)
    (G : X.Modules) :
    alternatingCechSheafPresheafZero U G ≫ alternatingCechSheafPresheafD U G 0 = 0 := by
  classical
  apply Pi.hom_ext
  intro t
  rw [Category.assoc, alternatingCechSheafPresheafD_π]
  simp only [Preadditive.comp_sum, Preadditive.comp_zsmul, ← Category.assoc,
    alternatingCechSheafPresheafZero, Pi.lift_comp_π, cechCapModuleUnit_comp, Limits.zero_comp]
  simp [Fin.sum_univ_two]

/-- Degreewise module sheafification of the explicit presheaf complex.
Source: Stacks 01FM (blueprint: def-pc-s3-alternating-cech-sheaf-construction). -/
def alternatingCechSheafComplex {r : ℕ} (U : Fin r → X.Opens) (G : X.Modules) :
    CochainComplex X.Modules ℕ :=
  letI : (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).Additive :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).left_adjoint_additive
  ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj (alternatingCechSheafPresheafComplex U G)

/-- The augmentation obtained by sheafifying the restriction maps.
Source: Stacks 01FM (blueprint: def-pc-s3-alternating-cech-sheaf-construction). -/
def alternatingCechSheafAugmentation {r : ℕ} (U : Fin r → X.Opens) (G : X.Modules) :
    (CochainComplex.single₀ X.Modules).obj G ⟶ alternatingCechSheafComplex U G :=
  let L := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  letI : L.Additive :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).left_adjoint_additive
  let η : G ⟶ L.obj G.val := (SheafOfModules.fullyFaithfulForget _).preimage
    ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app G.val)
  (CochainComplex.fromSingle₀Equiv (alternatingCechSheafComplex U G) G).symm
    ⟨η ≫ L.map (alternatingCechSheafPresheafZero U G), by
      change (η ≫ L.map (alternatingCechSheafPresheafZero U G)) ≫
        L.map (alternatingCechSheafPresheafD U G 0) = 0
      rw [Category.assoc, ← L.map_comp, alternatingCechSheafPresheafZero_comp,
        L.map_zero, Limits.comp_zero]⟩

end
end AlgebraicGeometry

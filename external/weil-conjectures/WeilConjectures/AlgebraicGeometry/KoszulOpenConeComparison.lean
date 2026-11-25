/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KoszulOpenSystem
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone

/-! # The cone of the negative Koszul tail augmentation

Source: Stacks Project, Section 36.9, Tag 08CX, opening construction
(blueprint: lem-sc-koszul-open-cone-comparison).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

noncomputable section

private abbrev tail
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A) (e : ℕ) :=
  (koszulOpenTail A r f e).extend ComplexShape.embeddingDownNat
private abbrev single (A : Type u) [CommRing A] :=
  ((ChainComplex.single₀ (ModuleCat.{u} A)).obj (ModuleCat.of A A)).extend
    ComplexShape.embeddingDownNat
private abbrev full
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A) (e : ℕ) :=
  (ExteriorAlgebra.koszulComplex A r (fun i ↦ f i ^ (e + 1))).extend
    ComplexShape.embeddingDownNat
private abbrev aug
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A) (e : ℕ) :=
  HomologicalComplex.extendMap (koszulOpenAugmentation A r f e)
    ComplexShape.embeddingDownNat

private theorem extend_positive_zero (A : Type u) [CommRing A]
    (K : ChainComplex (ModuleCat.{u} A) ℕ)
    (n : ℤ) (hn : 0 < n) :
    CategoryTheory.Limits.IsZero ((K.extend ComplexShape.embeddingDownNat).X n) := by
  apply HomologicalComplex.isZero_extend_X
  intro i hi
  simp only [ComplexShape.embeddingDownNat_f] at hi
  omega

private theorem single_negative_zero (A : Type u) [CommRing A] (n : ℕ) :
    CategoryTheory.Limits.IsZero ((single A).X (-(n + 1 : ℕ))) := by
  refine (HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega : n + 1 ≠ 0)).of_iso
    (HomologicalComplex.extendXIso _ ComplexShape.embeddingDownNat rfl)

private def negativeTermIso
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A) (e : ℕ) (n : ℕ) :
    (tail A r f e).X (-(n : ℤ)) ≅ (full A r f e).X (-(n + 1 : ℕ)) :=
  (HomologicalComplex.extendXIso _ ComplexShape.embeddingDownNat rfl) ≪≫
    (HomologicalComplex.extendXIso
      (ExteriorAlgebra.koszulComplex A r (fun i ↦ f i ^ (e + 1)))
      ComplexShape.embeddingDownNat (i := n + 1) rfl).symm

private def zeroTermIso
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A) (e : ℕ) :
    (single A).X 0 ≅ (full A r f e).X 0 :=
  (HomologicalComplex.extendXIso _ ComplexShape.embeddingDownNat (i := 0) (by simp)) ≪≫
    (exteriorPower.zeroEquiv (R := A) (M := Fin r →₀ A)).toModuleIso.symm ≪≫
    (HomologicalComplex.extendXIso
      (ExteriorAlgebra.koszulComplex A r (fun i ↦ f i ^ (e + 1)))
      ComplexShape.embeddingDownNat (i := 0) (by simp)).symm

private def coneTermIso
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A) (e : ℕ) (n : ℤ) :
    (CochainComplex.mappingCone (aug A r f e)).X n ≅ (full A r f e).X n := by
  cases n with
  | ofNat n =>
    cases n with
    | zero =>
      exact HomologicalComplex.homotopyCofiber.XIsoBiprod (aug A r f e) 0 1 rfl ≪≫
        (CategoryTheory.Limits.isoZeroBiprod (extend_positive_zero A _ 1 (by omega))).symm ≪≫
        zeroTermIso A r f e
    | succ n =>
      change (CochainComplex.mappingCone (aug A r f e)).X (↑n + 1) ≅
        (full A r f e).X (↑n + 1)
      apply CategoryTheory.Limits.IsZero.iso
      · rw [CochainComplex.mappingCone.isZero_X_iff]
        exact ⟨extend_positive_zero A _ _ (by omega),
          extend_positive_zero A _ _ (by omega)⟩
      · exact extend_positive_zero A _ _ (by omega)
  | negSucc n =>
    exact HomologicalComplex.homotopyCofiber.XIsoBiprod (aug A r f e)
        (-(n + 1 : ℕ)) (-(n : ℤ)) (by simp) ≪≫
      (CategoryTheory.Limits.isoBiprodZero (single_negative_zero A n)).symm ≪≫
        negativeTermIso A r f e n

private theorem coneTermIso_negative_hom
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A) (e : ℕ) (n : ℕ) :
    (coneTermIso A r f e (-(n + 1 : ℕ))).hom =
      HomologicalComplex.homotopyCofiber.fstX (aug A r f e)
        (-(n + 1 : ℕ)) (-(n : ℤ)) (by simp) ≫ (negativeTermIso A r f e n).hom := by
  rfl

private theorem coneTermIso_zero_hom
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A) (e : ℕ) :
    (coneTermIso A r f e 0).hom =
      HomologicalComplex.homotopyCofiber.sndX (aug A r f e) 0 ≫
        (zeroTermIso A r f e).hom := by
  change (HomologicalComplex.homotopyCofiber.XIsoBiprod (aug A r f e) 0 1 rfl).hom ≫
    CategoryTheory.Limits.biprod.snd ≫ (zeroTermIso A r f e).hom = _
  apply HomologicalComplex.homotopyCofiber.ext_from_X (aug A r f e) 1 0 (by decide)
  · rw [HomologicalComplex.homotopyCofiber.inlX_XIsoBiprod_hom_assoc]
    simp
  · rw [HomologicalComplex.homotopyCofiber.inrX_XIsoBiprod_hom_assoc]
    simp

set_option backward.isDefEq.respectTransparency false in
private theorem negativeTermIso_comm
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A) (e : ℕ) (n : ℕ) :
    (tail A r f e).d (-(n + 1 : ℕ)) (-(n : ℤ)) ≫
        (negativeTermIso A r f e n).hom =
      -((negativeTermIso A r f e (n + 1)).hom ≫
        (full A r f e).d (-(n + 2 : ℕ)) (-(n + 1 : ℕ))) := by
  dsimp only [tail, full]
  rw [HomologicalComplex.extend_d_eq (koszulOpenTail A r f e)
    ComplexShape.embeddingDownNat
    (i := n + 1) (j := n)
    (show ComplexShape.embeddingDownNat.f (n + 1) = -(n + 1 : ℕ) from rfl)
    (show ComplexShape.embeddingDownNat.f n = -(n : ℤ) from rfl),
    HomologicalComplex.extend_d_eq
      (ExteriorAlgebra.koszulComplex A r (fun i ↦ f i ^ (e + 1)))
      ComplexShape.embeddingDownNat (i := n + 2) (j := n + 1)
      (show ComplexShape.embeddingDownNat.f (n + 2) = -(n + 2 : ℕ) from rfl)
      (show ComplexShape.embeddingDownNat.f (n + 1) = -(n + 1 : ℕ) from rfl)]
  dsimp only [negativeTermIso, Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  change _ ≫ (koszulOpenTail A r f e).d (n + 1) n ≫ _ =
    -(_ ≫ (ExteriorAlgebra.koszulComplex A r (fun i ↦ f i ^ (e + 1))).d
      (n + 2) (n + 1) ≫ _)
  dsimp only [koszulOpenTail, ExteriorAlgebra.koszulComplex, ChainComplex.of]
  erw [ChainComplex.of_d _ _ n, ChainComplex.of_d _ _ (n + 1)]
  simp only [Preadditive.comp_neg, Preadditive.neg_comp]

set_option backward.isDefEq.respectTransparency false in
private theorem augmentation_zeroTermIso
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A) (e : ℕ) :
    (aug A r f e).f 0 ≫ (zeroTermIso A r f e).hom =
      (negativeTermIso A r f e 0).hom ≫ (full A r f e).d (-1) 0 := by
  rw [HomologicalComplex.extendMap_f _ ComplexShape.embeddingDownNat
      (i := 0) (by simp),
    HomologicalComplex.extend_d_eq
      (ExteriorAlgebra.koszulComplex A r (fun i ↦ f i ^ (e + 1)))
      ComplexShape.embeddingDownNat (i := 1) (j := 0)
      (show ComplexShape.embeddingDownNat.f 1 = -1 from rfl)
      (show ComplexShape.embeddingDownNat.f 0 = 0 from rfl)]
  dsimp only [zeroTermIso, negativeTermIso, Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  simp only [koszulOpenAugmentation, ChainComplex.toSingle₀Equiv_symm_apply_f_zero,
    koszulOpenAugmentationComponent, Category.assoc, Iso.hom_inv_id_assoc]
  dsimp only [ExteriorAlgebra.koszulComplex, ChainComplex.of]
  erw [ChainComplex.of_d _ _ 0]

private theorem coneTermIso_comm_negative
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A) (e : ℕ) (n : ℕ) :
    (coneTermIso A r f e (-(n + 2 : ℕ))).hom ≫
        (full A r f e).d (-(n + 2 : ℕ)) (-(n + 1 : ℕ)) =
      (CochainComplex.mappingCone (aug A r f e)).d (-(n + 2 : ℕ)) (-(n + 1 : ℕ)) ≫
        (coneTermIso A r f e (-(n + 1 : ℕ))).hom := by
  rw [coneTermIso_negative_hom A r f e (n + 1), coneTermIso_negative_hom]
  change _ = HomologicalComplex.homotopyCofiber.d _ _ _ ≫ _
  rw [← Category.assoc, HomologicalComplex.homotopyCofiber.d_fstX (aug A r f e)
    (-(n + 2 : ℕ)) (-(n + 1 : ℕ)) (-(n : ℤ))
    (by simp only [ComplexShape.up_Rel, Nat.cast_add, Nat.cast_ofNat]; omega)
    (by simp)]
  simp only [Category.assoc, Preadditive.neg_comp]
  rw [negativeTermIso_comm, Preadditive.comp_neg, neg_neg]

private theorem coneTermIso_comm_zero
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A) (e : ℕ) :
    (coneTermIso A r f e (-1)).hom ≫ (full A r f e).d (-1) 0 =
      (CochainComplex.mappingCone (aug A r f e)).d (-1) 0 ≫
        (coneTermIso A r f e 0).hom := by
  have hzero := coneTermIso_negative_hom A r f e 0
  change (coneTermIso A r f e (-1)).hom =
    HomologicalComplex.homotopyCofiber.fstX (aug A r f e) (-1) 0 (by decide) ≫
      (negativeTermIso A r f e 0).hom at hzero
  rw [hzero, coneTermIso_zero_hom]
  change _ = HomologicalComplex.homotopyCofiber.d _ _ _ ≫ _
  rw [← Category.assoc, HomologicalComplex.homotopyCofiber.d_sndX (aug A r f e)
    (-1) 0 (by decide)]
  simp only [HomologicalComplex.extend_single_d, CategoryTheory.Limits.comp_zero,
    add_zero, Category.assoc]
  rw [augmentation_zeroTermIso]

private theorem coneTermIso_comm
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A) (e : ℕ)
    (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    (coneTermIso A r f e i).hom ≫ (full A r f e).d i j =
      (CochainComplex.mappingCone (aug A r f e)).d i j ≫
        (coneTermIso A r f e j).hom := by
  have hi : i = j - 1 := by
    simp only [ComplexShape.up_Rel] at hij
    omega
  subst i
  cases j with
  | ofNat j =>
    cases j with
    | zero => exact coneTermIso_comm_zero A r f e
    | succ j =>
      apply (extend_positive_zero A _ (↑j + 1) (by omega)).eq_of_tgt
  | negSucc j =>
    convert coneTermIso_comm_negative A r f e j using 1 <;> congr 1

/-- The cone of the tail augmentation is the full Koszul complex, compatibly
with the inclusion of its degree-zero term.
Source: Stacks Project, Section 36.9, Tag 08CX, opening construction
(blueprint: lem-sc-koszul-open-cone-comparison).

Proof: Let u be the extended tail augmentation. The cone in degree n is
I^(n+1) ⊕ A[0]^n. For n < 0 the second summand is zero and the first is
K^n; for n = 0 the first summand is zero and the second is A. For n > 0
both summands are zero. Identify the nonzero summand with K^n, using the
inverse of exteriorPower.zeroEquiv in degree zero. The inverse uses the
appropriate biproduct inclusion. The cone differential on the first
summand is the negative of the tail differential, hence the original
Koszul differential. From degree -1 to degree zero the off-diagonal cone
differential is the augmentation, which becomes the Koszul boundary under
the degree-zero identification. All other off-diagonal components vanish.
Thus these degreewise inverse maps commute with differentials and define
an isomorphism of complexes. The right cone inclusion is zero off degree
zero and in degree zero becomes precisely koszulOpenKoszulInclusion,
which proves the asserted equality of chain maps. This also covers r = 0:
the tail is zero and the cone is A[0]. For the zero ring all terms are zero
and the same construction applies. -/
theorem koszulOpen_module_cone_comparison
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A) (e : ℕ) :
    let u := HomologicalComplex.extendMap (koszulOpenAugmentation A r f e)
      ComplexShape.embeddingDownNat
    ∃ c : CochainComplex.mappingCone u ≅
        (ExteriorAlgebra.koszulComplex A r (fun i ↦ f i ^ (e + 1))).extend
          ComplexShape.embeddingDownNat,
      CochainComplex.mappingCone.inr u ≫ c.hom =
        HomologicalComplex.extendMap (koszulOpenKoszulInclusion A r f e)
          ComplexShape.embeddingDownNat := by
  let c := HomologicalComplex.Hom.isoOfComponents (coneTermIso A r f e)
    (coneTermIso_comm A r f e)
  refine ⟨c, ?_⟩
  apply HomologicalComplex.hom_ext
  intro n
  change (CochainComplex.mappingCone.inr (aug A r f e)).f n ≫
    (coneTermIso A r f e n).hom = _
  cases n with
  | ofNat n =>
    cases n with
    | zero =>
      change (CochainComplex.mappingCone.inr (aug A r f e)).f 0 ≫
        (coneTermIso A r f e 0).hom =
        (HomologicalComplex.extendMap (koszulOpenKoszulInclusion A r f e)
          ComplexShape.embeddingDownNat).f 0
      rw [coneTermIso_zero_hom]
      change HomologicalComplex.homotopyCofiber.inrX (aug A r f e) 0 ≫
        HomologicalComplex.homotopyCofiber.sndX (aug A r f e) 0 ≫
          (zeroTermIso A r f e).hom = _
      rw [HomologicalComplex.homotopyCofiber.inrX_sndX_assoc]
      rw [HomologicalComplex.extendMap_f _ ComplexShape.embeddingDownNat
        (i := 0) (show ComplexShape.embeddingDownNat.f 0 = 0 from rfl)]
      dsimp only [zeroTermIso, Iso.trans_hom, Iso.symm_hom]
      simp only [koszulOpenKoszulInclusion,
        ChainComplex.fromSingle₀Equiv_symm_apply_f_zero]
    | succ n =>
      exact (extend_positive_zero A _ (↑n + 1) (by omega)).eq_of_src _ _
  | negSucc n => exact (single_negative_zero A n).eq_of_src _ _

end

end AlgebraicGeometry

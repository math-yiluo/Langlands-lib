/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Weil.WeilFiniteKoszulTensorModel
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import WeilConjectures.AlgebraicGeometry.Weil.WeilKoszulAdjoinGenerator

/-! # The algebraic exterior-to-tensor comparison

Source: Stacks Project, More on Algebra, Tag 0664, lemma-join-sequences-koszul-complex.
(blueprint: lem-weil-pbc-exterior-negative-koszul-tensor).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme

private theorem emptyKoszul_isZero
    {A : Type (u + 1)} [CommRing A] (a : Fin 0 → A) (m : ℕ) (i : ℤ) (hi : i ≠ 0) :
    IsZero ((completedKoszulPower (A := A) 0 a m).X i) := by
  classical
  by_cases hp : 0 < i
  · apply HomologicalComplex.isZero_extend_X
    intro q
    change -(q : ℤ) ≠ i
    omega
  · let q := (-i).toNat
    have hq : ComplexShape.embeddingDownNat.f q = i := by
      change -(q : ℤ) = i
      dsimp [q]
      omega
    have hqpos : 0 < q := by dsimp [q]; omega
    have : IsEmpty (Set.powersetCard (Fin 0) q) := ⟨fun s ↦ by
      have h := Finset.card_le_univ s.val
      have hs : s.val.card = q := s.property
      simp only [Fintype.card_fin, hs] at h
      omega⟩
    let b := (Finsupp.basisSingleOne :
      Module.Basis (Fin 0) A (Fin 0 →₀ A)).exteriorPower q
    have : Subsingleton (⋀[A]^q (Fin 0 →₀ A)) := b.repr.injective.subsingleton
    exact (ModuleCat.isZero_of_subsingleton (ModuleCat.of A (⋀[A]^q (Fin 0 →₀ A)))).of_iso
      ((ExteriorAlgebra.koszulComplex A 0 (fun k ↦ a k ^ (m + 1))).extendXIso
        ComplexShape.embeddingDownNat hq)

private def emptyKoszulIso {A : Type (u + 1)} [CommRing A] (a : Fin 0 → A) (m : ℕ) :
    completedKoszulPower (A := A) 0 a m ≅ finiteNegativeKoszulTensor 0 a m :=
  HomologicalComplex.Hom.isoOfComponents (fun i ↦
    if hi : i = 0 then
      (HomologicalComplex.XIsoOfEq _ hi) ≪≫
        ((ExteriorAlgebra.koszulComplex A 0 (fun k ↦ a k ^ (m + 1))).extendXIso
          ComplexShape.embeddingDownNat (i := 0) rfl) ≪≫
        (exteriorPower.zeroEquiv A (Fin 0 →₀ A)).toModuleIso ≪≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ModuleCat.of A A)).symm ≪≫
        (HomologicalComplex.XIsoOfEq _ hi).symm
    else
      (emptyKoszul_isZero a m i hi).iso
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 (ModuleCat.of A A) i hi))
    (by
      intro i j hij
      by_cases hj : j = 0
      · have hi : i ≠ 0 := by change i + 1 = j at hij; omega
        exact (emptyKoszul_isZero a m i hi).eq_of_src _ _
      · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0
          (ModuleCat.of A A) j hj).eq_of_tgt _ _)

private theorem emptyKoszulIso_hom_f_zero {A : Type (u + 1)} [CommRing A]
    (a : Fin 0 → A) (m : ℕ) :
    (emptyKoszulIso a m).hom.f 0 =
      ((ExteriorAlgebra.koszulComplex A 0 (fun k ↦ a k ^ (m + 1))).extendXIso
        ComplexShape.embeddingDownNat (i := 0) rfl).hom ≫
      (exteriorPower.zeroEquiv A (Fin 0 →₀ A)).toModuleIso.hom ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ModuleCat.of A A)).inv := by
  simp [emptyKoszulIso]

/-- Joining one-generator exterior complexes gives the exterior complex of the list.

Source: Stacks Project, More on Algebra, Tag 0664, lemma-join-sequences-koszul-complex.
(blueprint: lem-weil-pbc-exterior-negative-koszul-tensor).

Proof: split the ordered basis Fin (r+1) into its first vector and its tail.
In exterior degree k, separate the increasing k-subsets according as they contain
that first vector. The two summands are the tail exterior powers of degrees k and
k-1, respectively. Send a wedge not containing the first vector to 1 tensor that
wedge, and a wedge containing it to that vector tensor the remaining wedge. The
inverse concatenates the wedges, so both composites are identity on the ordered
subset bases. Contraction of a wedge containing the first vector is the first
coefficient times its tail minus the first vector wedged with tail contraction;
this is exactly the total differential, whose sign on the first degree -1
summand is minus. On the other summand both differentials are tail contraction.
This constructs the chain isomorphism for adjoining one generator. Induct on r,
starting from the exterior degree-zero identification with A and the vanishing
of all positive exterior powers of the zero module. Extension to integer degrees
by zero preserves the formulas. The diagonal exterior transition multiplies a
subset by the product of its a_i, which is also the tensor transition. The empty
subset maps to the tensor of empty subsets with coefficient 1, giving the unit
identity. These computations use no division, regularity or nonzero coefficient;
they hold over the zero ring and for empty lists. -/
theorem exteriorNegativeKoszulTensorComparison
    {A : Type (u + 1)} [CommRing A] (r : ℕ) (a : Fin r → A) :
    ∃ e : ∀ m : ℕ, completedKoszulPower (A := A) r a m ≅
        finiteNegativeKoszulTensor r a m,
      (∀ m, completedKoszulTransition (A := A) r a m ≫ (e m).hom =
        (e (m + 1)).hom ≫ finiteNegativeKoszulTransition r a m) ∧
      (∀ m, finiteKoszulExteriorUnitZero r a m ≫ (e m).hom.f 0 =
        finiteNegativeKoszulUnitZero r a m)  := by
  induction r with
  | zero =>
    refine ⟨emptyKoszulIso a, ?_, ?_⟩
    · intro m
      apply HomologicalComplex.to_single_hom_ext
      simp only [HomologicalComplex.comp_f, emptyKoszulIso_hom_f_zero,
        finiteNegativeKoszulTransition, Category.comp_id]
      erw [completedKoszulTransition,
        HomologicalComplex.extendMap_f _ _ (i := 0) (i' := 0) rfl]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      have h := exteriorPower.zeroEquiv_naturality (completedKoszulGenerator (A := A) 0 a)
      have h' : ModuleCat.ofHom (exteriorPower.map 0
          (completedKoszulGenerator (A := A) 0 a)) ≫
            (exteriorPower.zeroEquiv A (Fin 0 →₀ A)).toModuleIso.hom =
          (exteriorPower.zeroEquiv A (Fin 0 →₀ A)).toModuleIso.hom := by
        apply ModuleCat.hom_ext
        exact h
      rw [← Category.assoc _ _
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (ModuleCat.of A A)).inv, h']
    · intro m
      rw [emptyKoszulIso_hom_f_zero]
      dsimp only [finiteKoszulExteriorUnitZero, finiteNegativeKoszulUnitZero]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      change (exteriorPower.zeroEquiv A (Fin 0 →₀ A)).toModuleIso.inv ≫
        (exteriorPower.zeroEquiv A (Fin 0 →₀ A)).toModuleIso.hom ≫ _ = _
      rw [Iso.inv_hom_id_assoc]
  | succ r ih =>
    obtain ⟨e, he, heu⟩ := koszulAdjoinGenerator r a
    obtain ⟨t, ht, htu⟩ := ih (fun i ↦ a i.succ)
    let B := (curriedTensor (ModuleCat.{u + 1} A)).map₂HomologicalComplex
      (.up ℤ) (.up ℤ) (.up ℤ)
    let s := fun m ↦ (B.obj
      (completedKoszulPower (A := A) 1 (fun _ ↦ a 0) m)).mapIso (t m)
    refine ⟨fun m ↦ e m ≪≫ s m, ?_, ?_⟩
    · intro m
      dsimp only [Iso.trans_hom]
      rw [← Category.assoc, he m]
      simp only [Category.assoc]
      apply congrArg ((e (m + 1)).hom ≫ ·)
      change
        (completedKoszulTransition (A := A) 1 (fun _ ↦ a 0) m ⊗ₘ
            completedKoszulTransition (A := A) r (fun i ↦ a i.succ) m) ≫
          (𝟙 _ ⊗ₘ (t m).hom) =
        (𝟙 _ ⊗ₘ (t (m + 1)).hom) ≫
          (completedKoszulTransition (A := A) 1 (fun _ ↦ a 0) m ⊗ₘ
            finiteNegativeKoszulTransition r (fun i ↦ a i.succ) m)
      simp only [tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp, ht m]
    · intro m
      dsimp only [Iso.trans_hom, HomologicalComplex.comp_f]
      rw [← Category.assoc, heu m]
      dsimp only [finiteNegativeKoszulTensor, finiteNegativeKoszulUnitZero]
      change _ ≫ _ ≫ _ ≫ (HomologicalComplex.tensorHom (𝟙 _) (t m).hom).f 0 = _
      simp only [HomologicalComplex.ιTensorObj, HomologicalComplex.tensorHom]
      rw [HomologicalComplex.ι_mapBifunctorMap]
      simp only [HomologicalComplex.id_f, curriedTensor_map_app,
        curriedTensor_obj_map, id_whiskerRight]
      erw [Category.id_comp]
      rw [tensorHom_comp_whiskerLeft_assoc, htu m]

end AlgebraicGeometry.Scheme

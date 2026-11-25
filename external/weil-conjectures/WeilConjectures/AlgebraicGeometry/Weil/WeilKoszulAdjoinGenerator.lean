/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Weil.WeilFiniteKoszulTensorModel
import WeilConjectures.AlgebraicGeometry.Weil.WeilKoszulJoinBijective
import WeilConjectures.AlgebraicGeometry.Weil.WeilKoszulJoinLeibniz

/-! # Adjoining one generator to an exterior Koszul complex

Source: Stacks Project, More on Algebra, Tag 0664, lemma-join-sequences-koszul-complex.
(blueprint: lem-weil-pbc-koszul-adjoin-generator).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

variable {A : Type (u + 1)} [CommRing A]

private theorem exteriorMap_coe {E F : Type (u + 1)} [AddCommGroup E] [Module A E]
    [AddCommGroup F] [Module A F] (g : E →ₗ[A] F) (n : ℕ) (x : ⋀[A]^n E) :
    (exteriorPower.map n g x : ExteriorAlgebra A F) =
      ExteriorAlgebra.map g (x : ExteriorAlgebra A E) := by
  have h : (⋀[A]^n F).subtype.comp (exteriorPower.map n g) =
      (ExteriorAlgebra.map g).toLinearMap.comp (⋀[A]^n E).subtype := by
    apply exteriorPower.linearMap_ext
    ext v
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      exteriorPower.map_apply_ιMulti, Submodule.subtype_apply,
      exteriorPower.ιMulti_apply_coe,
      AlgHom.toLinearMap_apply, ExteriorAlgebra.map_apply_ιMulti]
  exact LinearMap.congr_fun h x

private theorem joinWedge_tmul (r n k : ℕ)
    (x : ⋀[A]^n (Fin 1 →₀ A)) (y : ⋀[A]^k (Fin r →₀ A)) :
    (koszulJoinWedge r n k (x ⊗ₜ[A] y) : ExteriorAlgebra A (Fin (r + 1) →₀ A)) =
      ExteriorAlgebra.map (koszulHeadInclusion r) x.val *
        ExteriorAlgebra.map (koszulTailInclusion r) y.val := by
  rw [koszulJoinWedge_tmul_coe, exteriorMap_coe, exteriorMap_coe]

private theorem head_diagonal (r : ℕ) (a : Fin (r + 1) → A) :
    (completedKoszulGenerator (r + 1) a).comp (koszulHeadInclusion r) =
      (koszulHeadInclusion r).comp (completedKoszulGenerator 1 (fun _ ↦ a 0)) := by
  apply Finsupp.lhom_ext
  intro j c
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  simp [completedKoszulGenerator, koszulHeadInclusion]

private theorem tail_diagonal (r : ℕ) (a : Fin (r + 1) → A) :
    (completedKoszulGenerator (r + 1) a).comp (koszulTailInclusion r) =
      (koszulTailInclusion r).comp
        (completedKoszulGenerator r (fun j ↦ a j.succ)) := by
  apply Finsupp.lhom_ext
  intro j c
  simp [completedKoszulGenerator, koszulTailInclusion]

private theorem joinWedge_diagonal (r n k : ℕ) (a : Fin (r + 1) → A) :
    (koszulJoinWedge r n k).comp
        (TensorProduct.map
          (exteriorPower.map n (completedKoszulGenerator 1 (fun _ ↦ a 0)))
          (exteriorPower.map k (completedKoszulGenerator r (fun j ↦ a j.succ)))) =
      (exteriorPower.map (n + k) (completedKoszulGenerator (r + 1) a)).comp
        (koszulJoinWedge r n k) := by
  apply TensorProduct.ext'
  intro x y
  apply Subtype.ext
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul, joinWedge_tmul,
    exteriorMap_coe, map_mul]
  have hh := congrArg (fun f : ExteriorAlgebra A (Fin 1 →₀ A) →ₐ[A]
      ExteriorAlgebra A (Fin (r + 1) →₀ A) ↦ f x.val)
    (show (ExteriorAlgebra.map (completedKoszulGenerator (r + 1) a)).comp
        (ExteriorAlgebra.map (koszulHeadInclusion r)) =
      (ExteriorAlgebra.map (koszulHeadInclusion r)).comp
        (ExteriorAlgebra.map (completedKoszulGenerator 1 (fun _ ↦ a 0))) by
          rw [ExteriorAlgebra.map_comp_map, ExteriorAlgebra.map_comp_map, head_diagonal])
  have ht := congrArg (fun f : ExteriorAlgebra A (Fin r →₀ A) →ₐ[A]
      ExteriorAlgebra A (Fin (r + 1) →₀ A) ↦ f y.val)
    (show (ExteriorAlgebra.map (completedKoszulGenerator (r + 1) a)).comp
        (ExteriorAlgebra.map (koszulTailInclusion r)) =
      (ExteriorAlgebra.map (koszulTailInclusion r)).comp
        (ExteriorAlgebra.map (completedKoszulGenerator r (fun j ↦ a j.succ))) by
          rw [ExteriorAlgebra.map_comp_map, ExteriorAlgebra.map_comp_map, tail_diagonal])
  exact congrArg₂ (· * ·) hh.symm ht.symm

private theorem transition_component (r : ℕ) (a : Fin r → A) (m n : ℕ)
    (i : ℤ) (hi : ComplexShape.embeddingDownNat.f n = i) :
    (completedKoszulTransition (A := A) r a m).f i =
      ((ExteriorAlgebra.koszulComplex A r (fun j ↦ a j ^ (m + 2))).extendXIso
        ComplexShape.embeddingDownNat hi).hom ≫
      ModuleCat.ofHom (exteriorPower.map n (completedKoszulGenerator r a)) ≫
      ((ExteriorAlgebra.koszulComplex A r (fun j ↦ a j ^ (m + 1))).extendXIso
        ComplexShape.embeddingDownNat hi).inv := by
  exact HomologicalComplex.extendMap_f _ ComplexShape.embeddingDownNat hi

private theorem joinSummand_transition (r : ℕ) (a : Fin (r + 1) → A)
    (m : ℕ) (p q i : ℤ) (hi : p + q = i) :
    ((completedKoszulTransition (A := A) 1 (fun _ ↦ a 0) m).f p ⊗ₘ
      (completedKoszulTransition (A := A) r (fun j ↦ a j.succ) m).f q) ≫
        koszulJoinSummand r a m p q i hi =
      koszulJoinSummand r a (m + 1) p q i hi ≫
        (completedKoszulTransition (A := A) (r + 1) a m).f i := by
  by_cases hp : p ≤ 0
  · by_cases hq : q ≤ 0
    · have hnp : ComplexShape.embeddingDownNat.f (-p).toNat = p := by
        change -(((-p).toNat : ℕ) : ℤ) = p
        omega
      have hnq : ComplexShape.embeddingDownNat.f (-q).toNat = q := by
        change -(((-q).toNat : ℕ) : ℤ) = q
        omega
      have hni : ComplexShape.embeddingDownNat.f ((-p).toNat + (-q).toNat) = i := by
        change -(((-p).toNat + (-q).toNat : ℕ) : ℤ) = i
        omega
      rw [transition_component 1 _ m _ p hnp, transition_component r _ m _ q hnq,
        transition_component (r + 1) _ m _ i hni]
      simp only [koszulJoinSummand, dite_eq_left hp, dite_eq_left hq, koszulGradedTermIso,
        tensorHom_comp_tensorHom_assoc, Category.assoc, Iso.inv_hom_id_assoc,
        Iso.inv_hom_id, Category.comp_id]
      rw [← tensorHom_comp_tensorHom_assoc]
      have hw :
          (ModuleCat.ofHom
              (exteriorPower.map (-p).toNat (completedKoszulGenerator 1 (fun _ ↦ a 0))) ⊗ₘ
            ModuleCat.ofHom
              (exteriorPower.map (-q).toNat
                (completedKoszulGenerator r (fun j ↦ a j.succ)))) ≫
              ModuleCat.ofHom (koszulJoinWedge r (-p).toNat (-q).toNat) =
          ModuleCat.ofHom (koszulJoinWedge r (-p).toNat (-q).toNat) ≫
            ModuleCat.ofHom
              (exteriorPower.map ((-p).toNat + (-q).toNat)
                (completedKoszulGenerator (r + 1) a)) := by
        apply ModuleCat.hom_ext
        exact joinWedge_diagonal r (-p).toNat (-q).toNat a
      simpa only [Category.assoc, koszulGradedTermIso] using
        congrArg (fun f ↦
          ((koszulGradedTermIso 1 (fun _ ↦ a 0) (m + 1) p hp).hom ⊗ₘ
            (koszulGradedTermIso r (fun j ↦ a j.succ) (m + 1) q hq).hom) ≫ f ≫
          ((ExteriorAlgebra.koszulComplex A (r + 1) (fun j ↦ a j ^ (m + 1))).extendXIso
            ComplexShape.embeddingDownNat hni).inv) hw
    · simp [koszulJoinSummand, hp, hq]
  · simp [koszulJoinSummand, hp]

/-- Exterior multiplication commutes with all power transitions.
Source: Stacks, Tag 0664 (blueprint: def-weil-pbc-koszul-join-graded). -/
private theorem koszulJoinGraded_transition (r : ℕ) (a : Fin (r + 1) → A) (m : ℕ) (i : ℤ) :
    (HomologicalComplex.tensorHom
      (completedKoszulTransition (A := A) 1 (fun _ ↦ a 0) m)
      (completedKoszulTransition (A := A) r (fun j ↦ a j.succ) m)).f i ≫
        koszulJoinGraded r a m i =
      koszulJoinGraded r a (m + 1) i ≫
        (completedKoszulTransition (A := A) (r + 1) a m).f i := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  simp only [koszulJoinGraded, HomologicalComplex.ι_mapBifunctorDesc_assoc,
    HomologicalComplex.ι_mapBifunctorMap_assoc, curriedTensor_map_app,
    curriedTensor_obj_map]
  rw [← tensorHom_def_assoc, HomologicalComplex.ι_mapBifunctorDesc]
  exact joinSummand_transition r a m p q i hpq

private theorem zeroEquiv_symm_coe (s : ℕ) (c : A) :
    ((exteriorPower.zeroEquiv A (Fin s →₀ A)).symm c :
        ExteriorAlgebra A (Fin s →₀ A)) = algebraMap A _ c := by
  rw [exteriorPower.zeroEquiv_symm_apply]
  change c • (ExteriorAlgebra.ιMulti A 0 _) = _
  rw [ExteriorAlgebra.ιMulti_zero_apply, Algebra.smul_def, mul_one]

/-- Multiplication sends the tensor of the exterior units to the exterior unit.
Source: Stacks, Tag 0664 (blueprint: def-weil-pbc-koszul-join-graded). -/
private theorem koszulJoinGraded_unit (r : ℕ) (a : Fin (r + 1) → A) (m : ℕ) :
    (ρ_ (ModuleCat.of A A)).inv ≫
        (finiteKoszulExteriorUnitZero 1 (fun _ ↦ a 0) m ⊗ₘ
          finiteKoszulExteriorUnitZero r (fun j ↦ a j.succ) m) ≫
        HomologicalComplex.ιTensorObj
          (completedKoszulPower (A := A) 1 (fun _ ↦ a 0) m)
          (completedKoszulPower (A := A) r (fun j ↦ a j.succ) m) 0 0 0 (by omega) ≫
        koszulJoinGraded r a m 0 = finiteKoszulExteriorUnitZero (r + 1) a m := by
  apply (cancel_mono
    ((ExteriorAlgebra.koszulComplex A (r + 1) (fun j ↦ a j ^ (m + 1))).extendXIso
      ComplexShape.embeddingDownNat (i := 0) rfl).hom).mp
  simp only [koszulJoinGraded, Category.assoc, HomologicalComplex.ι_mapBifunctorDesc_assoc]
  simp only [koszulJoinSummand, le_refl, dite_eq_left,
    finiteKoszulExteriorUnitZero, koszulGradedTermIso, tensorHom_comp_tensorHom_assoc,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  change (koszulJoinWedge r 0 0
      ((exteriorPower.zeroEquiv A (Fin 1 →₀ A)).symm c ⊗ₜ[A]
        (exteriorPower.zeroEquiv A (Fin r →₀ A)).symm 1)) =
    (exteriorPower.zeroEquiv A (Fin (r + 1) →₀ A)).symm c
  apply Subtype.ext
  rw [joinWedge_tmul, zeroEquiv_symm_coe, zeroEquiv_symm_coe, zeroEquiv_symm_coe]
  simp

private def koszulJoinMap {A : Type (u + 1)} [CommRing A]
    (r : ℕ) (a : Fin (r + 1) → A) (m : ℕ) :
    HomologicalComplex.tensorObj
      (completedKoszulPower (A := A) 1 (fun _ ↦ a 0) m)
      (completedKoszulPower (A := A) r (fun j ↦ a j.succ) m) ⟶
        completedKoszulPower (A := A) (r + 1) a m where
  f i := koszulJoinGraded r a m i
  comm' i j hij := by
    have hj : i + 1 = j := hij
    subst j
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    have hi : p + q = i := hpq
    subst i
    simp only [koszulJoinGraded, HomologicalComplex.ι_mapBifunctorDesc_assoc]
    rw [HomologicalComplex.mapBifunctor.d_eq]
    simp only [Preadditive.comp_add, Preadditive.add_comp,
      HomologicalComplex.mapBifunctor.ι_D₁_assoc,
      HomologicalComplex.mapBifunctor.ι_D₂_assoc]
    rw [HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _
        (show (ComplexShape.up ℤ).Rel p (p + 1) from rfl) q
        (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) (p, q) + 1) (by
          change p + 1 + q = p + q + 1; omega),
      HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ p
        (show (ComplexShape.up ℤ).Rel q (q + 1) from rfl)
        (ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) (p, q) + 1) (by
          change p + (q + 1) = p + q + 1; omega)]
    simp only [show ComplexShape.ε₁ (.up ℤ) (.up ℤ) (.up ℤ) (p, q) = 1 from rfl,
      one_smul, Linear.units_smul_comp, Category.assoc,
      HomologicalComplex.ι_mapBifunctorDesc, curriedTensor_map_app,
      curriedTensor_obj_map, ← tensorHom_id, ← id_tensorHom]
    exact koszulJoinSummand_leibniz r a m p q

private theorem koszulJoinMap_transition {A : Type (u + 1)} [CommRing A]
    (r : ℕ) (a : Fin (r + 1) → A) (m : ℕ) :
    HomologicalComplex.tensorHom
        (completedKoszulTransition (A := A) 1 (fun _ ↦ a 0) m)
        (completedKoszulTransition (A := A) r (fun j ↦ a j.succ) m) ≫
      koszulJoinMap r a m =
    koszulJoinMap r a (m + 1) ≫ completedKoszulTransition (A := A) (r + 1) a m := by
  apply HomologicalComplex.hom_ext
  intro i
  exact koszulJoinGraded_transition r a m i

private instance koszulJoinMap_isIso {A : Type (u + 1)} [CommRing A]
    (r : ℕ) (a : Fin (r + 1) → A) (m : ℕ) : IsIso (koszulJoinMap r a m) := by
  have (i : ℤ) : IsIso ((koszulJoinMap r a m).f i) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (koszulJoinGraded_bijective r a m i)
  exact HomologicalComplex.Hom.isIso_of_components _

/-- Splitting off the first exterior generator gives a tensor with a rank-one complex.

Source: Stacks Project, More on Algebra, Tag 0664, lemma-join-sequences-koszul-complex.
(blueprint: lem-weil-pbc-koszul-adjoin-generator).

Proof: split the ordered free basis Fin (r+1) into its first vector and its tail.
In exterior degree k, separate increasing k-subsets according as they contain the
first vector. Send a wedge without it to 1 tensor the tail wedge, and a wedge
with it to the first vector tensor the remaining wedge. The inverse concatenates
wedges; the two maps are inverse on the ordered subset bases, over any ring.
Contraction of a wedge with the first vector is its first coefficient times the
tail minus the first vector wedged with tail contraction. This is exactly the
total differential on the first degree -1 summand. Without that vector it is
tail contraction. Extension by zero to integer degrees respects these formulas.
The exterior transition on a subset is multiplication by the product of its
coefficients, equal to the product of the first and tail transition factors.
The empty subset maps to 1 tensor 1, proving the unit equation. The same basis
maps apply when k=0 or k>r+1, the tail is empty, coefficients vanish or are units,
and over the zero ring. No sheaf transport or dual complex is involved. -/
theorem koszulAdjoinGenerator
    {A : Type (u + 1)} [CommRing A] (r : ℕ) (a : Fin (r + 1) → A) :
    ∃ e : ∀ m : ℕ, completedKoszulPower (A := A) (r + 1) a m ≅
        HomologicalComplex.tensorObj
          (completedKoszulPower (A := A) 1 (fun _ ↦ a 0) m)
          (completedKoszulPower (A := A) r (fun i ↦ a i.succ) m),
      (∀ m, completedKoszulTransition (A := A) (r + 1) a m ≫ (e m).hom =
        (e (m + 1)).hom ≫ HomologicalComplex.tensorHom
          (completedKoszulTransition (A := A) 1 (fun _ ↦ a 0) m)
          (completedKoszulTransition (A := A) r (fun i ↦ a i.succ) m)) ∧
      (∀ m, finiteKoszulExteriorUnitZero (r + 1) a m ≫ (e m).hom.f 0 =
        (ρ_ (ModuleCat.of A A)).inv ≫
          (finiteKoszulExteriorUnitZero 1 (fun _ ↦ a 0) m ⊗ₘ
            finiteKoszulExteriorUnitZero r (fun i ↦ a i.succ) m) ≫
          HomologicalComplex.ιTensorObj
            (completedKoszulPower (A := A) 1 (fun _ ↦ a 0) m)
            (completedKoszulPower (A := A) r (fun i ↦ a i.succ) m) 0 0 0 (by omega)) := by
  let e (m : ℕ) := (asIso (koszulJoinMap r a m)).symm
  refine ⟨e, ?_, ?_⟩
  · intro m
    apply (cancel_mono (koszulJoinMap r a m)).mp
    change completedKoszulTransition (A := A) (r + 1) a m ≫
        inv (koszulJoinMap r a m) ≫ koszulJoinMap r a m =
      (inv (koszulJoinMap r a (m + 1)) ≫ _) ≫ koszulJoinMap r a m
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    rw [koszulJoinMap_transition, IsIso.inv_hom_id_assoc]
  · intro m
    apply (cancel_mono ((koszulJoinMap r a m).f 0)).mp
    have hcancel : (e m).hom.f 0 ≫ (koszulJoinMap r a m).f 0 = 𝟙 _ := by
      exact congrArg (fun f ↦ f.f 0) (IsIso.inv_hom_id (koszulJoinMap r a m))
    rw [Category.assoc, hcancel, Category.comp_id]
    simpa only [Category.assoc, koszulJoinMap] using (koszulJoinGraded_unit r a m).symm

end AlgebraicGeometry.Scheme

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicKoszulCompletion
public import Mathlib.CategoryTheory.Functor.OfSequence
import all WeilConjectures.AlgebraicGeometry.Koszul.KoszulQuotientLimit
import all WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicKoszulCompletion

/-! # The graded nilpotent Koszul tower
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section
set_option autoImplicit false
universe t
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry.Scheme
attribute [local instance] koszulConstantFunctor_preservesZero

variable (B : Type t) [CommRing B] (r : ℕ) (b : Fin r → B)
private theorem generator_single (j : Fin r) (c : ULift.{t + 1} B) :
    koszulPowerGenerator B r b (Finsupp.single j c) =
      Finsupp.single j (c * ULift.up (b j)) := by
  simp [koszulPowerGenerator, Finsupp.linearCombination_single]
private theorem generator_pow_single (k : ℕ) (j : Fin r) (c : ULift.{t + 1} B) :
    (koszulPowerGenerator B r b ^ k) (Finsupp.single j c) =
      Finsupp.single j (c * ULift.up (b j ^ k)) := by
  induction k generalizing c with
  | zero =>
    simp only [pow_zero, Module.End.one_apply]
    congr 1
    apply ULift.ext
    simp
  | succ k ih =>
    rw [pow_succ]
    change (koszulPowerGenerator B r b ^ k)
      (koszulPowerGenerator B r b (Finsupp.single j c)) = _
    rw [generator_single, ih]
    congr 1
    apply ULift.ext
    simp [pow_succ, mul_assoc, mul_comm]
open CategoryTheory.Limits Opposite
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem coefficient_jump (n k q : ℕ) :
    let K := fun m ↦ ExteriorAlgebra.koszulComplex (ULift.{t + 1} B) r
      (fun j ↦ ULift.up (b j ^ (m + 1)))
    let e := fun m ↦ (K m).extendXIso ComplexShape.embeddingDownNat (i := q) rfl
    let T := Functor.ofOpSequence (koszulPowerTransition B r b)
    (T.map (homOfLE (Nat.le_add_right n k)).op).f
      (ComplexShape.embeddingDownNat.f q) =
      (e (n + k)).hom ≫ ModuleCat.ofHom
        (exteriorPower.map q (koszulPowerGenerator B r b ^ k)) ≫ (e n).inv := by
  dsimp only
  let K := fun m ↦ ExteriorAlgebra.koszulComplex (ULift.{t + 1} B) r
    (fun j ↦ ULift.up (b j ^ (m + 1)))
  let e := fun m ↦ (K m).extendXIso ComplexShape.embeddingDownNat (i := q) rfl
  let T := Functor.ofOpSequence (koszulPowerTransition B r b)
  change (T.map _).f _ = (e (n + k)).hom ≫ _ ≫ (e n).inv
  have hstep (m : ℕ) : (koszulPowerTransition B r b m).f (ComplexShape.embeddingDownNat.f q) =
      (e (m + 1)).hom ≫ ModuleCat.ofHom
        (exteriorPower.map q (koszulPowerGenerator B r b)) ≫ (e m).inv := by
    dsimp only [koszulPowerTransition]
    exact HomologicalComplex.extendMap_f _ ComplexShape.embeddingDownNat rfl
  induction k with
  | zero =>
    have hm : (homOfLE (Nat.le_add_right n 0)).op = 𝟙 (op n) := Subsingleton.elim _ _
    rw [hm]
    erw [T.map_id]
    rw [HomologicalComplex.id_f, pow_zero]
    change 𝟙 _ = (e n).hom ≫ ModuleCat.ofHom (exteriorPower.map q LinearMap.id) ≫ (e n).inv
    rw [exteriorPower.map_id]
    change 𝟙 _ = (e n).hom ≫ 𝟙 _ ≫ (e n).inv
    rw [Category.id_comp, Iso.hom_inv_id]
  | succ k ih =>
    have hm : (homOfLE (Nat.le_add_right n (k + 1))).op =
        (homOfLE (Nat.le_succ (n + k))).op ≫
          (homOfLE (Nat.le_add_right n k)).op := Subsingleton.elim _ _
    rw [hm, T.map_comp, HomologicalComplex.comp_f, ih]
    dsimp only [T]
    rw [Functor.ofOpSequence_map_homOfLE_succ]
    erw [hstep]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [pow_succ]
    change _ = _ ≫ ModuleCat.ofHom
      (exteriorPower.map q ((koszulPowerGenerator B r b ^ k).comp
        (koszulPowerGenerator B r b))) ≫ _
    rw [exteriorPower.map_comp, ModuleCat.ofHom_comp]
    simp only [Category.assoc]
    rfl

variable (X : Scheme.{t}) (B : Type t) [CommRing B]
  (r : ℕ) (b : Fin r → B)
  (C : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X B)) ℤ)

end AlgebraicGeometry.Scheme

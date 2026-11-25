/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Weil.WeilKoszulJoinGraded

/-! # Positive-degree vanishing for graded exterior multiplication

The positive-degree part of `koszulJoinGraded_bijective` is a zero-object
argument. (blueprint: new-weil-pbc-koszul-join-graded-positive)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

private theorem completedKoszulPower_isZero_of_pos
    {A : Type (u + 1)} [CommRing A] (s : ℕ) (a : Fin s → A)
    (m : ℕ) (i : ℤ) (hi : 0 < i) :
    IsZero ((completedKoszulPower (A := A) s a m).X i) := by
  apply HomologicalComplex.isZero_extend_X
  intro n h
  change -((n : ℕ) : ℤ) = i at h
  omega

private theorem koszulJoinTensor_isZero_of_pos
    {A : Type (u + 1)} [CommRing A] (r : ℕ) (a : Fin (r + 1) → A)
    (m : ℕ) (i : ℤ) (hi : 0 < i) :
    IsZero ((HomologicalComplex.tensorObj
      (completedKoszulPower (A := A) 1 (fun _ ↦ a 0) m)
      (completedKoszulPower (A := A) r (fun j ↦ a j.succ) m)).X i) := by
  let K := completedKoszulPower (A := A) 1 (fun _ ↦ a 0) m
  let L := completedKoszulPower (A := A) r (fun j ↦ a j.succ) m
  let X : GradedObject (ℤ × ℤ) (ModuleCat.{u + 1} A) :=
    fun z ↦ K.X z.1 ⊗ L.X z.2
  let p : ℤ × ℤ → ℤ := fun z ↦ z.1 + z.2
  change IsZero ((X.mapObj p) i)
  apply (GradedObject.isColimitCofanMapObj X p i).isZero_pt
  apply Functor.isZero
  intro z
  dsimp [X, p]
  by_cases hp : 0 < z.as.1.1
  · exact (MonoidalCategory.tensorRight (L.X z.as.1.2)).map_isZero
      (completedKoszulPower_isZero_of_pos 1 (fun _ ↦ a 0) m z.as.1.1 hp)
  · have hq : 0 < z.as.1.2 := by
      have hz := z.as.2
      change p z.as.1 = i at hz
      dsimp [p] at hz
      omega
    exact (MonoidalCategory.tensorLeft (K.X z.as.1.1)).map_isZero
      (completedKoszulPower_isZero_of_pos r (fun j ↦ a j.succ) m z.as.1.2 hq)

/-- In positive cochain degree both the total tensor term and the target term
are zero, hence the graded join map is bijective. The proof uses the defining
extension by zero of `completedKoszulPower` and the coproduct description of a
homological tensor term. -/
theorem koszulJoinGraded_bijective_of_pos
    {A : Type (u + 1)} [CommRing A] (r : ℕ) (a : Fin (r + 1) → A)
    (m : ℕ) (i : ℤ) (hi : 0 < i) :
    Function.Bijective (koszulJoinGraded r a m i).hom := by
  have hs := koszulJoinTensor_isZero_of_pos r a m i hi
  have ht := completedKoszulPower_isZero_of_pos (r + 1) a m i hi
  exact (ConcreteCategory.isIso_iff_bijective _).mp
    (isIso_of_source_target_iso_zero _ hs.isoZero ht.isoZero)

end AlgebraicGeometry.Scheme

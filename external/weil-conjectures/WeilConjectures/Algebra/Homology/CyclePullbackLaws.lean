/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.CyclePullbackTower

/-!
# Equations for the explicit cycle-pullback tower

Source: Stacks Project, Derived Categories, Lemma 05T7 (1), the descending step.
-/

@[expose] public section

universe v u vB uB
open CategoryTheory CategoryTheory.Limits
namespace CochainComplex.CyclePullback

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {B : Type uB} [Category.{vB} B]

private theorem pair_square (T : A ⥤ A) (π : T ⟶ 𝟭 A)
    {F : B ⥤ CochainComplex A ℤ} (s t : Stage F) (h : s = step T π t) :
    s.d ≫ eqToHom (show s.next = t.current from by rw [h]; rfl) ≫ t.d = 0 := by
  subst s
  simpa using step_square T π t

private theorem pair_comm (T : A ⥤ A) (π : T ⟶ 𝟭 A)
    {F : B ⥤ CochainComplex A ℤ} (s t : Stage F) (h : s = step T π t) :
    s.e ≫ targetD F s.degree t.degree =
      s.d ≫ eqToHom (show s.next = t.current from by rw [h]; rfl) ≫ t.e := by
  subst s
  simpa only [step, eqToHom_refl, Category.id_comp] using step_comm T π t

private theorem target_transport (F : B ⥤ CochainComplex A ℤ)
    (a b i j : ℤ) (ha : a = i) (hb : b = j) :
    eqToHom (congrArg (targetTerm F) ha) ≫ targetD F i j =
      targetD F a b ≫ eqToHom (congrArg (targetTerm F) hb) := by
  subst i j
  simp

private theorem square_below (T : A ⥤ A) (π : T ⟶ 𝟭 A)
    (F : B ⥤ CochainComplex A ℤ) (N i : ℤ) (hi : i < N) :
    differential T π F N i ≫ differential T π F N (i + 1) = 0 := by
  have hi' : i ≤ N := by omega
  have hn : i + 1 ≤ N := by omega
  have hd : depth N i = depth N (i + 1) + 1 := by unfold depth; omega
  have hs : tower T π F N (depth N i) = step T π (tower T π F N (depth N (i + 1))) := by
    rw [hd]; rfl
  have h := pair_square T π _ _ hs
  dsimp only [differential]
  rw [dite_eq_left hi', dite_eq_left hn]
  simp only [Category.assoc, eqToHom_trans_assoc]
  have h' := congrArg (fun f ↦ eqToHom (term_eq T π F N i hi') ≫ f ≫
    eqToHom (tower_next T π F N (i + 1) hn)) h
  simpa only [Category.assoc, comp_zero, zero_comp] using h'

private theorem comm_below (T : A ⥤ A) (π : T ⟶ 𝟭 A)
    (F : B ⥤ CochainComplex A ℤ) (N i : ℤ) (hi : i < N) :
    augmentation T π F N i ≫ targetD F i (i + 1) =
      differential T π F N i ≫ augmentation T π F N (i + 1) := by
  have hi' : i ≤ N := by omega
  have hn : i + 1 ≤ N := by omega
  have hd : depth N i = depth N (i + 1) + 1 := by unfold depth; omega
  have hs : tower T π F N (depth N i) = step T π (tower T π F N (depth N (i + 1))) := by
    rw [hd]; rfl
  have h := pair_comm T π _ _ hs
  dsimp only [differential, augmentation]
  rw [dite_eq_left hi', dite_eq_left hn, dite_eq_left hi']
  simp only [Category.assoc, eqToHom_trans_assoc]
  rw [target_transport F _ _ i (i + 1) (degree_eq T π F N i hi')
    (degree_eq T π F N (i + 1) hn)]
  have h' := congrArg (fun f ↦ eqToHom (term_eq T π F N i hi') ≫ f ≫
    eqToHom (congrArg (targetTerm F) (degree_eq T π F N (i + 1) hn))) h
  simpa only [Category.assoc] using h'

private theorem comm_top (T : A ⥤ A) (π : T ⟶ 𝟭 A)
    (F : B ⥤ CochainComplex A ℤ) (N : ℤ) :
    augmentation T π F N N ≫ targetD F N (N + 1) =
      differential T π F N N ≫ augmentation T π F N (N + 1) := by
  have hi : N ≤ N := le_refl N
  have hs : tower T π F N (depth N N) = step T π (initial F N) := by
    simp [depth, tower]
  have h : (tower T π F N (depth N N)).e ≫
      targetD F (tower T π F N (depth N N)).degree (N + 1) = 0 := by
    simpa only [initial, comp_zero] using pair_comm T π _ _ hs
  have hz : augmentation T π F N (N + 1) = 0 := by
    simp only [augmentation, dite_eq_right (by omega : ¬ N + 1 ≤ N)]
  rw [hz, comp_zero]
  dsimp only [augmentation]
  rw [dite_eq_left hi]
  simp only [Category.assoc]
  rw [target_transport F _ (N + 1) N (N + 1) (degree_eq T π F N N hi) rfl]
  simpa only [Category.assoc, comp_zero, eqToHom_refl, Category.comp_id] using
    congrArg (fun f ↦ eqToHom (term_eq T π F N N hi) ≫ f) h

/-- The integer-indexed differentials square to zero and commute with the augmentation.

Source: Stacks Project, Derived Categories, Lemma 05T7 (1).
(blueprint: lem-pc-cycle-pullback-tower-laws-stage3).

Proof: In a successor stage the differential is pi, followed by the second pullback
projection and the inclusion of the kernel of the preceding stage's differential.
Thus its composite with that preceding differential is zero by the kernel equation.
The first projection followed by the target differential equals the second projection
followed by the kernel inclusion and the preceding augmentation, by the pullback
condition. Precompose this equation by pi. For integer degree i below N, the tower
index in degree i+1 is one less than the index in degree i, so the two equations
transport to exactly the displayed equations. At i=N the next terms are zero;
the same calculation uses the initial stage. Above N all differentials and
augmentations are zero, and both equations follow from composition with zero. -/
theorem tower_laws {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type uB} [Category.{vB} B] (T : A ⥤ A) (π : T ⟶ 𝟭 A)
    (F : B ⥤ CochainComplex A ℤ) (N : ℤ) :
    ∀ i : ℤ,
      differential T π F N i ≫ differential T π F N (i + 1) = 0 ∧
      augmentation T π F N i ≫ targetD F i (i + 1) =
        differential T π F N i ≫ augmentation T π F N (i + 1) := by
  intro i
  by_cases hi : i < N
  · exact ⟨square_below T π F N i hi, comm_below T π F N i hi⟩
  · by_cases h : i = N
    · subst i
      refine ⟨?_, comm_top T π F N⟩
      have hz : differential T π F N (N + 1) = 0 := by
        simp only [differential, dite_eq_right (by omega : ¬ N + 1 ≤ N)]
      rw [hz, comp_zero]
    · have hni : ¬ i ≤ N := by omega
      simp [differential, augmentation, hni]

end CochainComplex.CyclePullback

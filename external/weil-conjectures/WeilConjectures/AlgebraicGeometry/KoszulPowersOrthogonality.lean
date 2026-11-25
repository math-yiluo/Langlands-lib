/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.KoszulComplex
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Homology.Embedding.CochainComplex

import WeilConjectures.AlgebraicGeometry.KoszulCoordinateMulTriangle

/-! # Koszul orthogonality propagates to positive powers
Source: Stacks Project, Tag 09IR.
(blueprint: lem-pc-koszul-powers-orthogonality).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- Orthogonality to every shift persists after raising the generators to positive powers.
Source: Stacks Project, Tag 09IR, proof of lemma-orthogonal-koszul-complex;
Tag 062C, lemma-koszul-mult.
(blueprint: lem-pc-koszul-powers-orthogonality).

Proof: Induct on the sum of the positive exponents minus r. The zero case has every
exponent equal to one, so it is the hypothesis. Otherwise select a coordinate with
exponent m+1, m positive, and use the Koszul multiplication triangle for f_i^m and
f_i, with all other entries fixed. Its two outer Koszul objects have smaller sums.
The long exact Hom sequence, in all integer shifts, makes the middle Hom group zero.
Tensoring the one-variable triangle with the remaining finite free Koszul factors,
then sheafifying and localizing, gives the required triangle for any coordinate.
The argument also applies to an empty tuple, zero ring, or zero generators. -/
theorem koszul_powers_orthogonal_of_orthogonal
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    (E : schemeDerivedCategory (Spec (.of A)))
    (horth : ∀ n : ℤ, Subsingleton ((DerivedCategory.Q.obj
          ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A)
            (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
            _ _ _ _ (tilde.functor (.of A))
            ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ)).obj
            ((ExteriorAlgebra.koszulComplex A r f).extend
              ComplexShape.embeddingDownNat)))⟦n⟧ ⟶ E))
    (e : Fin r → ℕ) (he : ∀ i, 0 < e i) (n : ℤ) :
    Subsingleton ((DerivedCategory.Q.obj
          ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A)
            (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
            _ _ _ _ (tilde.functor (.of A))
            ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ)).obj
            ((ExteriorAlgebra.koszulComplex A r (fun i ↦ f i ^ e i)).extend
              ComplexShape.embeddingDownNat)))⟦n⟧ ⟶ E) := by
  classical
  let K := fun g : Fin r → A ↦ DerivedCategory.Q.obj
    ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A)
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
      _ _ _ _ (tilde.functor (.of A))
      ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ)).obj
      ((ExteriorAlgebra.koszulComplex A r g).extend
        ComplexShape.embeddingDownNat))
  change Subsingleton ((K (fun i ↦ f i ^ e i))⟦n⟧ ⟶ E)
  have hpow : ∀ s : ℕ, ∀ e : Fin r → ℕ, (∀ i, 0 < e i) →
      (∑ i, e i) = s → ∀ n : ℤ,
        Subsingleton ((K (fun i ↦ f i ^ e i))⟦n⟧ ⟶ E) := by
    intro s
    induction s using Nat.strong_induction_on with
    | h s ih =>
      intro e he hs n
      by_cases hbase : ∀ i, e i = 1
      · have heq : (fun i ↦ f i ^ e i) = f := by
          ext i
          simp [hbase i]
        rw [heq]
        exact horth n
      · push Not at hbase
        obtain ⟨i, hi⟩ := hbase
        have hi' : 1 < e i := by have := he i; omega
        have hlt : ∀ m : ℕ, m < e i →
            (∑ j, Function.update e i m j) < s := by
          intro m hm
          rw [← hs]
          apply Finset.sum_lt_sum
          · intro j _
            by_cases hj : j = i
            · subst j
              simpa using hm.le
            · simp [Function.update_of_ne hj]
          · exact ⟨i, Finset.mem_univ i, by simpa using hm⟩
        have hpos : ∀ m : ℕ, 0 < m → ∀ j, 0 < Function.update e i m j := by
          intro m hm j
          by_cases hj : j = i
          · subst j; simpa using hm
          · simpa [Function.update_of_ne hj] using he j
        have hprev := ih _ (hlt (e i - 1) (by omega))
          (Function.update e i (e i - 1)) (hpos _ (by omega)) rfl n
        have hone := ih _ (hlt 1 hi') (Function.update e i 1)
          (hpos _ (by omega)) rfl n
        obtain ⟨α, β, δ, hT⟩ := koszul_coordinate_mul_triangle A r
          (fun j ↦ f j ^ e j) i (f i ^ (e i - 1)) (f i)
        have hleft : (fun j ↦ f j ^ Function.update e i (e i - 1) j) =
            Function.update (fun j ↦ f j ^ e j) i (f i ^ (e i - 1)) := by
          ext j
          by_cases hj : j = i <;> simp [hj]
        have hright : (fun j ↦ f j ^ Function.update e i 1 j) =
            Function.update (fun j ↦ f j ^ e j) i (f i) := by
          ext j
          by_cases hj : j = i <;> simp [hj]
        have hmiddle : Function.update (fun j ↦ f j ^ e j) i
            (f i ^ (e i - 1) * f i) = (fun j ↦ f j ^ e j) := by
          have hexp : e i - 1 + 1 = e i := by omega
          rw [← pow_succ, hexp]
          exact Function.update_eq_self i _
        rw [hleft] at hprev
        rw [hright] at hone
        let T := (shiftFunctor
          (Pretriangulated.Triangle (schemeDerivedCategory (Spec (.of A)))) n).obj
          (Pretriangulated.Triangle.mk α β δ)
        have hshift : T ∈ distTriang _ :=
          Pretriangulated.Triangle.shift_distinguished _ hT n
        have hvanish : Subsingleton (T.obj₂ ⟶ E) := by
          refine ⟨fun φ ψ ↦ ?_⟩
          have hz : ∀ θ : T.obj₂ ⟶ E, θ = 0 := by
            intro θ
            obtain ⟨η, hη⟩ := T.yoneda_exact₂ hshift θ (hprev.elim _ _)
            rw [hη, hone.elim η 0, comp_zero]
          exact (hz φ).trans (hz ψ).symm
        change Subsingleton ((K (Function.update (fun j ↦ f j ^ e j) i
          (f i ^ (e i - 1) * f i)))⟦n⟧ ⟶ E) at hvanish
        rwa [hmiddle] at hvanish
  exact hpow _ e he rfl n

end AlgebraicGeometry

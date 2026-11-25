/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.ExtremallyDisconnected
public import Mathlib.Algebra.Homology.ShortComplex.Exact
import WeilConjectures.Topology.IntegralContinuousPresentationComplete

/-! # Completion for a finite presentation by a compact projective generator -/

@[expose] public section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

/-- Compatible morphisms into a finite cokernel presentation have a limit when
endomorphisms of the projective generator are continuous functions into a compact ring.
Source: Hemo--Richarz--Scholbach, Proposition 5.1, finite-presentation chart argument.
(blueprint: lem-sp-integral-projective-presentation-complete).

Proof. Lift each morphism through the finite free presentation by projectivity.
Lift each scalar-divisible difference by exactness of the scalar cokernel sequence,
and lift the remaining presentation relation. The endomorphism-ring equivalence
turns these lifts into continuous matrix congruences. Compact matrix completeness
produces a vector satisfying all of them. Its image in the presentation cokernel
has the prescribed reductions: matrix terms vanish and each remaining correction
is divisible by the required scalar power. -/
theorem exists_cokernel_limit_of_continuous_end
    {C : Type*} [Category C] [Abelian C] [HasFiniteBiproducts C] (P : C) [Projective P]
    {S : Type*} {R : Type} [TopologicalSpace S] [CompactSpace S] [T2Space S]
    [ExtremallyDisconnected S] [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [CompactSpace R] [T2Space R]
    (e : C(S, R) ≃+* End P) (r : ℕ)
    {n m : ℕ} (A : (⨁ fun _ : Fin m ↦ P) ⟶ ⨁ fun _ : Fin n ↦ P)
    (x : ℕ → (P ⟶ cokernel A))
    (hx : ∀ k l : ℕ, k ≤ l →
      x l ≫ cokernel.π (r ^ (k + 1) • 𝟙 (cokernel A)) =
        x k ≫ cokernel.π (r ^ (k + 1) • 𝟙 (cokernel A))) :
    ∃ z : P ⟶ cokernel A, ∀ k : ℕ,
      z ≫ cokernel.π (r ^ (k + 1) • 𝟙 (cokernel A)) =
        x k ≫ cokernel.π (r ^ (k + 1) • 𝟙 (cokernel A)) := by
  classical
  let y (k : ℕ) := Projective.factorThru (x k) (cokernel.π A)
  have hy (k : ℕ) : y k ≫ cokernel.π A = x k := Projective.factorThru_comp _ _
  let t : Matrix (Fin n) (Fin m) C(S, R) := fun i j ↦
    e.symm (.of (biproduct.ι (fun _ ↦ P) j ≫ A ≫ biproduct.π (fun _ ↦ P) i))
  let b (k : ℕ) : Fin n → C(S, R) := fun i ↦
    e.symm (.of (y k ≫ biproduct.π (fun _ ↦ P) i))
  have hsum {p : ℕ} {Y Z : C} (f : Y ⟶ ⨁ fun _ : Fin p ↦ P)
      (g : (⨁ fun _ : Fin p ↦ P) ⟶ Z) :
      f ≫ g = ∑ a, (f ≫ biproduct.π (fun _ ↦ P) a) ≫
        (biproduct.ι (fun _ ↦ P) a ≫ g) := by
    conv_lhs => rw [← Category.id_comp g, ← biproduct.total]
    rw [Preadditive.sum_comp, Preadditive.comp_sum]
    simp only [Category.assoc]
  have happ (z : P ⟶ ⨁ fun _ : Fin m ↦ P) (i : Fin n) :
      (e (∑ j, t i j * e.symm (.of (z ≫ biproduct.π (fun _ ↦ P) j)))).asHom =
        z ≫ A ≫ biproduct.π (fun _ ↦ P) i := by
    rw [map_sum, End.sum_asHom, hsum z (A ≫ biproduct.π (fun _ ↦ P) i)]
    apply Finset.sum_congr rfl
    intro j _
    simp only [map_mul, RingEquiv.apply_symm_apply, End.mul_asHom, t]
  have hb : ∀ k l : ℕ, k ≤ l →
      ∃ a : Fin m → C(S, R), ∃ c : Fin n → C(S, R),
        ∀ i, b l i = b k i + (∑ j, t i j * a j) + (r : R) ^ (k + 1) • c i := by
    intro k l hkl
    have hd₀ : (x l - x k) ≫ cokernel.π (r ^ (k + 1) • 𝟙 (cokernel A)) = 0 := by
      rw [Preadditive.sub_comp, hx k l hkl, sub_self]
    let d : P ⟶ cokernel A :=
      (ShortComplex.cokernelSequence_exact (r ^ (k + 1) • 𝟙 (cokernel A))).liftFromProjective
        (x l - x k) hd₀
    have hd : r ^ (k + 1) • d = x l - x k := by
      have h := (ShortComplex.cokernelSequence_exact
        (r ^ (k + 1) • 𝟙 (cokernel A))).liftFromProjective_comp (x l - x k) hd₀
      change d ≫ (r ^ (k + 1) • 𝟙 (cokernel A)) = x l - x k at h
      simpa only [Preadditive.comp_nsmul, Category.comp_id] using h
    let c := Projective.factorThru d (cokernel.π A)
    have hc : c ≫ cokernel.π A = d := Projective.factorThru_comp _ _
    have hz : (y l - y k - r ^ (k + 1) • c) ≫ cokernel.π A = 0 := by
      rw [Preadditive.sub_comp, Preadditive.sub_comp, Preadditive.nsmul_comp,
        hy, hy, hc, hd, sub_self]
    let z : P ⟶ ⨁ fun _ : Fin m ↦ P :=
      (ShortComplex.cokernelSequence_exact A).liftFromProjective _ hz
    have hza : z ≫ A = y l - y k - r ^ (k + 1) • c :=
      (ShortComplex.cokernelSequence_exact A).liftFromProjective_comp _ hz
    refine ⟨fun j ↦ e.symm (.of (z ≫ biproduct.π (fun _ ↦ P) j)),
      fun i ↦ e.symm (.of (c ≫ biproduct.π (fun _ ↦ P) i)), fun i ↦ ?_⟩
    apply e.injective
    apply End.ext
    rw [map_add, map_add, show (r : R) ^ (k + 1) •
      e.symm (.of (c ≫ biproduct.π (fun _ ↦ P) i)) =
      r ^ (k + 1) • e.symm (.of (c ≫ biproduct.π (fun _ ↦ P) i)) by
        rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul], map_nsmul,
      End.add_asHom, End.add_asHom, End.nsmul_asHom, happ,
      ← Category.assoc, hza, Preadditive.sub_comp, Preadditive.sub_comp,
      Preadditive.nsmul_comp]
    simp only [b, RingEquiv.apply_symm_apply]
    abel
  obtain ⟨v, hv⟩ := ContinuousMap.exists_matrix_limit_of_compatible t b (r : R) hb
  let z : P ⟶ ⨁ fun _ : Fin n ↦ P := biproduct.lift fun i ↦ (e (v i)).asHom
  refine ⟨z ≫ cokernel.π A, fun k ↦ ?_⟩
  obtain ⟨a, c, hac⟩ := hv k
  let za : P ⟶ ⨁ fun _ : Fin m ↦ P := biproduct.lift fun j ↦ (e (a j)).asHom
  let zc : P ⟶ ⨁ fun _ : Fin n ↦ P := biproduct.lift fun i ↦ (e (c i)).asHom
  have he : z = y k + za ≫ A + r ^ (k + 1) • zc := by
    apply biproduct.hom_ext
    intro i
    have hh := congrArg e (hac i)
    rw [map_add, map_add, show (r : R) ^ (k + 1) • c i =
      r ^ (k + 1) • c i by rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul], map_nsmul] at hh
    have hh := congrArg End.asHom hh
    simp only [End.add_asHom, End.nsmul_asHom] at hh
    have hha := happ za i
    simp only [za, biproduct.lift_π] at hha
    change (e (∑ j, t i j * e.symm (e (a j)))).asHom = _ at hha
    simp only [RingEquiv.symm_apply_apply] at hha
    rw [hha] at hh
    simpa only [z, zc, b, biproduct.lift_π, RingEquiv.apply_symm_apply,
      Preadditive.add_comp, Preadditive.nsmul_comp, Category.assoc] using hh
  have hza0 : (za ≫ A) ≫ cokernel.π A = 0 := by
    rw [Category.assoc, cokernel.condition, comp_zero]
  have hzsum : z ≫ cokernel.π A = x k + r ^ (k + 1) • (zc ≫ cokernel.π A) := by
    rw [he, Preadditive.add_comp, Preadditive.add_comp, Preadditive.nsmul_comp,
      hy, hza0, add_zero]
  rw [hzsum, Preadditive.add_comp]
  have hzsc : (r ^ (k + 1) • (zc ≫ cokernel.π A)) ≫
      cokernel.π (r ^ (k + 1) • 𝟙 (cokernel A)) = 0 := by
    calc
      _ = ((zc ≫ cokernel.π A) ≫ (r ^ (k + 1) • 𝟙 (cokernel A))) ≫
          cokernel.π (r ^ (k + 1) • 𝟙 (cokernel A)) := by
        rw [Preadditive.comp_nsmul, Category.comp_id]
      _ = 0 := by rw [Category.assoc, cokernel.condition, comp_zero]
  rw [hzsc, add_zero]

end CategoryTheory

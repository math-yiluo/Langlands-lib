/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-! # Pure boundaries of compatible multiplication sequences. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
namespace AlgebraicGeometry.ProEtale

private theorem scalar_square
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Preadditive A] [Preadditive B] [Preadditive C]
    (F : A ⥤ C) (G : B ⥤ C) [F.Additive] [G.Additive]
    (X : A) (Y : B) (f : F.obj X ⟶ G.obj Y) (n : ℕ) :
    F.map (n • 𝟙 X) ≫ f = f ≫ G.map (n • 𝟙 Y) := by
  simp only [Functor.map_nsmul, F.map_id, G.map_id, Preadditive.nsmul_comp,
    Preadditive.comp_nsmul, Category.id_comp, Category.comp_id]

/-- A compatible family of multiplication short exact sequences, whose quotients
are pure in degree minus two, has ordinary sheaf boundaries with multiplier ell. -/
theorem pure_multiplication_triangle_assembly
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w} A]
    (ℓ : ℕ) (P : CochainComplex A ℤ) (M : A) (H : ℕᵒᵖ ⥤ A)
    (e : DerivedCategory.Q.obj P ≅ ((DerivedCategory.singleFunctor A 0).obj M)⟦(1 : ℤ)⟧)
    (Q : ℕ → CochainComplex A ℤ) (q : ∀ n, P ⟶ Q n)
    (t : ∀ n, Q (n + 1) ⟶ Q n)
    (hz : ∀ n, (ℓ ^ (n + 1) • 𝟙 P) ≫ q n = 0)
    (hS : ∀ n, (ShortComplex.mk _ (q n) (hz n)).ShortExact)
    (ht : ∀ n, q (n + 1) ≫ t n = q n)
    (b : ∀ n, DerivedCategory.Q.obj (Q n) ≅
      ((DerivedCategory.singleFunctor A 0).obj (H.obj (op n)))⟦(2 : ℤ)⟧)
    (hb : ∀ n, DerivedCategory.Q.map (t n) ≫ (b n).hom =
      (b (n + 1)).hom ≫
        ((DerivedCategory.singleFunctor A 0).map
          (H.map (homOfLE (Nat.le_succ n)).op))⟦(2 : ℤ)⟧')
    (v : ∀ n, ((DerivedCategory.singleFunctor A 0).obj M)⟦(1 : ℤ)⟧ ⟶
      ((DerivedCategory.singleFunctor A 0).obj (H.obj (op n)))⟦(2 : ℤ)⟧)
    (hv : ∀ n, DerivedCategory.Q.map (q n) ≫ (b n).hom = e.hom ≫ v n) :
    ∃ d : ∀ n, H.obj (op n) ⟶ M,
      (∀ n, Triangle.mk
        (ℓ ^ (n + 1) • 𝟙 (((DerivedCategory.singleFunctor A 0).obj M)⟦(1 : ℤ)⟧))
        (v n)
        (((DerivedCategory.singleFunctor A 0).map (d n))⟦(2 : ℤ)⟧' ≫
          (shiftFunctorAdd (DerivedCategory A) (1 : ℤ) 1).hom.app
            ((DerivedCategory.singleFunctor A 0).obj M)) ∈ distTriang (DerivedCategory A)) ∧
      ∀ n, H.map (homOfLE (Nat.le_succ n)).op ≫ d n = d (n + 1) ≫ (ℓ • 𝟙 M) := by
  classical
  let F := DerivedCategory.singleFunctor A 0
  let F₂ := F ⋙ shiftFunctor (DerivedCategory A) (2 : ℤ)
  let a := (shiftFunctorAdd (DerivedCategory A) (1 : ℤ) 1).app (F.obj M)
  let S (n : ℕ) := ShortComplex.mk _ (q n) (hz n)
  let δ (n : ℕ) := (b n).inv ≫ DerivedCategory.triangleOfSESδ (hS n) ≫
    e.hom⟦(1 : ℤ)⟧'
  let d (n : ℕ) := F₂.preimage (δ n ≫ a.inv)
  have hd (n : ℕ) : F₂.map (d n) ≫ a.hom = δ n := by
    change F₂.map (F₂.preimage (δ n ≫ a.inv)) ≫ a.hom = δ n
    rw [F₂.map_preimage, Category.assoc, a.inv_hom_id]
    exact Category.comp_id _
  refine ⟨d, ?_, ?_⟩
  · intro n
    rw [show ((DerivedCategory.singleFunctor A 0).map (d n))⟦(2 : ℤ)⟧' ≫
        (shiftFunctorAdd (DerivedCategory A) (1 : ℤ) 1).hom.app
          ((DerivedCategory.singleFunctor A 0).obj M) = δ n from hd n]
    apply (distinguished_iff_of_iso
      (Triangle.isoMk (DerivedCategory.triangleOfSES (hS n))
        (Triangle.mk _ (v n) (δ n)) e e (b n) ?_ ?_ ?_)).1
      (DerivedCategory.triangleOfSES_distinguished (hS n))
    · change DerivedCategory.Q.map (ℓ ^ (n + 1) • 𝟙 P) ≫ e.hom =
        e.hom ≫ (ℓ ^ (n + 1) • 𝟙 _)
      rw [DerivedCategory.Q.map_nsmul,
        (DerivedCategory.Q : CochainComplex A ℤ ⥤ DerivedCategory A).map_id]
      simp only [Preadditive.comp_nsmul, Preadditive.nsmul_comp,
        Category.comp_id, Category.id_comp]
    · exact hv n
    · change DerivedCategory.triangleOfSESδ (hS n) ≫ e.hom⟦(1 : ℤ)⟧' =
        (b n).hom ≫ δ n
      simp only [δ, Iso.hom_inv_id_assoc]
  · intro n
    let φ : S (n + 1) ⟶ S n :=
      { τ₁ := ℓ • 𝟙 P
        τ₂ := 𝟙 P
        τ₃ := t n
        comm₁₂ := by
          dsimp [S]
          simp only [Preadditive.nsmul_comp, Category.id_comp, Category.comp_id,
            smul_smul, pow_succ, Nat.mul_comm]
        comm₂₃ := by simpa only [S, Category.id_comp] using (ht n).symm }
    have hδ :
        (F.map (H.map (homOfLE (Nat.le_succ n)).op))⟦(2 : ℤ)⟧' ≫ δ n =
          δ (n + 1) ≫ (ℓ • 𝟙 ((F.obj M)⟦(1 : ℤ)⟧))⟦(1 : ℤ)⟧' := by
      have h := DerivedCategory.triangleOfSESδ_naturality (hS (n + 1)) (hS n) φ
      change DerivedCategory.triangleOfSESδ (hS (n + 1)) ≫
        (DerivedCategory.Q.map (ℓ • 𝟙 P))⟦(1 : ℤ)⟧' =
          DerivedCategory.Q.map (t n) ≫ DerivedCategory.triangleOfSESδ (hS n) at h
      apply (cancel_epi (b (n + 1)).hom).1
      dsimp only [δ]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
      rw [← reassoc_of% (hb n)]
      simp only [Iso.hom_inv_id_assoc]
      rw [← reassoc_of% h]
      have hs := scalar_square DerivedCategory.Q (𝟭 (DerivedCategory A)) P
        ((F.obj M)⟦(1 : ℤ)⟧) e.hom ℓ
      change DerivedCategory.Q.map (ℓ • 𝟙 P) ≫ e.hom =
        e.hom ≫ (ℓ • 𝟙 ((F.obj M)⟦(1 : ℤ)⟧)) at hs
      rw [← Functor.map_comp, hs, Functor.map_comp]
    apply F₂.map_injective
    rw [F₂.map_comp, F₂.map_comp]
    apply (cancel_mono a.hom).1
    rw [Category.assoc, hd n]
    rw [Category.assoc (F₂.map (d (n + 1)))]
    rw [scalar_square F₂ (shiftFunctor (DerivedCategory A) (1 : ℤ)) M
      ((F.obj M)⟦(1 : ℤ)⟧) a.hom ℓ]
    rw [reassoc_of% (hd (n + 1))]
    simpa only [F₂, Functor.comp_map] using hδ

end AlgebraicGeometry.ProEtale

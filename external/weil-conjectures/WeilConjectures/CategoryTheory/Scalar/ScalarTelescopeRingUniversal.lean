/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.Preadditive
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# The ring universal property of a scalar telescope

Source: the ring-structure paragraph of the completed coefficient localization proof
(blueprint: lem-pe-scalar-telescope-ring-universal).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace CategoryTheory

private theorem scalar_leg_ext
    {C : Type u} [Category.{v} C] [Preadditive C]
    (l : ℕ) {X S T : C} (j : ℕ → (X ⟶ S))
    (hrec : ∀ n, l • j (n + 1) = j n)
    (hext : ∀ (f g : S ⟶ T), (∀ n, j n ≫ f = j n ≫ g) → f = g)
    [IsIso (l • 𝟙 T)] (f g : S ⟶ T) (h0 : j 0 ≫ f = j 0 ≫ g) : f = g := by
  apply hext f g
  intro n
  induction n with
  | zero => exact h0
  | succ n hn =>
    apply (cancel_mono (l • 𝟙 T)).1
    simpa only [Preadditive.comp_nsmul, Category.comp_id,
      ← Preadditive.nsmul_comp, hrec] using hn

private theorem scalar_leg_desc
    {C : Type u} [Category.{v} C] [Preadditive C]
    (l : ℕ) (X T : C) [IsIso (l • 𝟙 T)] (a : X ⟶ T) :
    ∃ j : ℕ → (X ⟶ T), j 0 = a ∧ ∀ n, l • j (n + 1) = j n := by
  let j : ℕ → (X ⟶ T) := Nat.rec a (fun _ f ↦ f ≫ inv (l • 𝟙 T))
  have hinv : l • inv (l • 𝟙 T) = 𝟙 T := by
    simpa only [Preadditive.nsmul_comp, Category.id_comp] using
      IsIso.hom_inv_id (l • 𝟙 T)
  refine ⟨j, rfl, ?_⟩
  intro n
  change l • (j n ≫ inv (l • 𝟙 T)) = j n
  rw [← Preadditive.comp_nsmul, hinv, Category.comp_id]

/-- A module telescope with ring zeroth leg is the ring localization at its scalar.
No commutativity of the test ring is required, since natural-number scalars are central.

Source: literature/blueprint/latest/blueprint/sec-proetale-coefficients/
sk-prop-sfb-qlbar-colimit-x/sk-prop-sfb-qlbar-colimit-x-invert-ell.proof.md,
paragraph Ring structure; the argument is the universal property of fractions
(blueprint: lem-pe-scalar-telescope-ring-universal).

Proof: Given a:R→B, restrict the regular B-module along a. The maps from the regular
R-module to B given by a followed by inverse multiplication by l to the nth power
are a cocone. The given module colimit gives a unique module map b:S→B extending it.
Its zeroth-leg equation gives preservation of the unit. To check multiplication,
tensor preserves colimits separately: compare on each pair of telescope legs.
The nth and mth legs are fractions with denominators l^n and l^m, and their product
is the (n+m)th leg applied to the product of the numerators. This identity follows
by cancelling invertible multiplication by l^(n+m) in S. The same identity holds
in B, proving multiplicativity of b. Finally any ring map extending a commutes with
multiplication by l and its inverse; it therefore agrees on all telescope legs.
The colimit property proves uniqueness. This also treats l=0: invertibility of
zero forces the relevant objects to be zero, and the argument is unchanged.
-/
theorem scalar_telescope_ring_universal
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C]
    [MonoidalPreadditive C] [HasColimitsOfShape ℕ C]
    [∀ A : C, PreservesColimitsOfShape ℕ (tensorLeft A)]
    [∀ A : C, PreservesColimitsOfShape ℕ (tensorRight A)]
    (l : ℕ) (R S : Mon C) (i : R ⟶ S)
    (ι : Functor.ofSequence (fun _ : ℕ ↦ l • 𝟙 (Mod.regular R.X)) ⟶
      (Functor.const ℕ).obj ((Mod.comap i.hom).obj (Mod.regular S.X)))
    (h0 : (ι.app 0).hom = i.hom)
    (hc : IsColimit (Cocone.mk ((Mod.comap i.hom).obj (Mod.regular S.X)) ι))
    (hi : IsIso (l • 𝟙 S.X)) :
    ∀ (B : Mon C), IsIso (l • 𝟙 B.X) →
      ∀ a : R ⟶ B, ∃! b : S ⟶ B, i ≫ b = a := by
  classical
  let := hi
  intro B hB a
  let := hB
  let c := (Mod.forget R.X).mapCocone
    (Cocone.mk ((Mod.comap i.hom).obj (Mod.regular S.X)) ι)
  have hc' : IsColimit c := isColimitOfPreserves (Mod.forget R.X) hc
  let j : ℕ → (R.X ⟶ S.X) := fun n ↦ (ι.app n).hom
  have hj : ∀ n, l • j (n + 1) = j n := by
    intro n
    have h := congrArg (fun f ↦ f.hom) (ι.naturality (homOfLE (Nat.le_succ n)))
    simp only [Functor.ofSequence_map_homOfLE_succ, Functor.const_obj_map,
      Mod.comp_hom', Mod.nsmul_hom, Mod.id_hom'] at h
    change (l • 𝟙 R.X) ≫ j (n + 1) = j n ≫ 𝟙 S.X at h
    simpa only [Preadditive.nsmul_comp, Category.id_comp, Category.comp_id] using h
  have hj0 : j 0 = i.hom := h0
  have ext₁ {T : C} [IsIso (l • 𝟙 T)] (f g : S.X ⟶ T)
      (h : i.hom ≫ f = i.hom ≫ g) : f = g := by
    apply scalar_leg_ext l j hj (fun f g h ↦ hc'.hom_ext h) f g
    simpa only [hj0] using h
  obtain ⟨k, hk0, hk⟩ := scalar_leg_desc l R.X B.X a.hom
  let d : Cocone ((Functor.ofSequence (fun _ : ℕ ↦ l • 𝟙 (Mod.regular R.X))) ⋙
      Mod.forget R.X) := Cocone.mk B.X (NatTrans.ofSequence k (fun n ↦ by
        simp only [Functor.comp_map, Functor.ofSequence_map_homOfLE_succ,
          Functor.const_obj_map]
        change (l • 𝟙 R.X) ≫ k (n + 1) = k n ≫ 𝟙 B.X
        simpa only [Preadditive.nsmul_comp, Category.id_comp, Category.comp_id] using hk n))
  let b : S.X ⟶ B.X := hc'.desc d
  have hb : i.hom ≫ b = a.hom := by
    have h := hc'.fac d 0
    change j 0 ≫ b = k 0 at h
    simpa only [hj0, hk0] using h
  have hmul : MonObj.mul (X := S.X) ≫ b = (b ⊗ₘ b) ≫ MonObj.mul := by
    apply scalar_leg_ext l (fun n ↦ j n ▷ S.X)
      (fun n ↦ by rw [← nsmul_whiskerRight, hj])
      (fun f g h ↦ (isColimitOfPreserves (tensorRight S.X) hc').hom_ext h)
    rw [hj0]
    apply scalar_leg_ext l (fun n ↦ R.X ◁ j n)
      (fun n ↦ by rw [← whiskerLeft_nsmul, hj])
      (fun f g h ↦ (isColimitOfPreserves (tensorLeft R.X) hc').hom_ext h)
    rw [hj0]
    simp only [← tensorHom_def'_assoc]
    rw [← IsMonHom.mul_hom_assoc, hb, tensorHom_comp_tensorHom_assoc]
    simpa only [hb] using IsMonHom.mul_hom a.hom
  let b' : S ⟶ B := Mon.Hom.mk' b (by
    rw [← IsMonHom.one_hom i.hom, Category.assoc, hb, IsMonHom.one_hom a.hom]) hmul
  refine ⟨b', Mon.Hom.ext hb, ?_⟩
  intro b'' h
  apply Mon.Hom.ext
  exact ext₁ b''.hom b (congrArg (fun f ↦ f.hom) h |>.trans hb.symm)

end CategoryTheory

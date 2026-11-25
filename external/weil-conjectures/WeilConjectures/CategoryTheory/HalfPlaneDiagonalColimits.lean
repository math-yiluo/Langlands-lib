/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.ExactCoupleConvergence

/-!
# Normalized colimits of half-plane exact-couple diagonals

Source: blueprint thm-sp-half-plane-convergence, proof paragraph 1, the stable diagonal.
(blueprint: lem-sp-half-plane-diagonal-colimits)
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.BigradedExactCouple

variable {C : Type u} [Category.{v} C] [Abelian C]

private theorem alpha_iso_left (X : BigradedExactCouple C 0)
    (hE : ∀ p q : ℤ, p < 0 → IsZero (X.E p q)) (p q : ℤ) (hp : p ≤ 0) :
    IsIso (X.alpha p q) := by
  obtain ⟨i, rfl⟩ : ∃ i : ℤ, p = i + 2 := ⟨p - 2, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j : ℤ, q = j - 1 := ⟨q + 1, by omega⟩
  have hker : kernelSubobject (X.alpha (i + 2) (j - 1)) = ⊥ := by
    have hz : X.f i j = 0 := (hE i j (by omega)).eq_zero_of_src _
    exact (X.exact_alpha i j).symm.trans (by rw [hz, imageSubobject_zero])
  have : Mono (X.alpha (i + 2) (j - 1)) :=
    Abelian.mono_of_kernel_ι_eq_zero _ (Subobject.mk_eq_bot_iff_zero.mp hker)
  have him : imageSubobject (X.alpha (i + 2) (j - 1)) = ⊤ := by
    have hz : X.g (i + 2 - 1) (j - 1 + 1) = 0 :=
      (hE _ _ (by omega)).eq_zero_of_tgt _
    simpa only [hz, kernelSubobject_zero] using X.exact_g (i + 2) (j - 1)
  apply (Subobject.isIso_iff_mk_eq_top _).mpr
  rwa [imageSubobject_mono] at him

private noncomputable def chainStep (Y : ℤ → C)
    (t : ∀ p : ℤ, Y (p + 1) ⟶ Y p) (p : ℤ) : Y p ⟶ Y (p - 1) :=
  eqToHom (congrArg Y (by omega)) ≫ t (p - 1)

private noncomputable def chainMaps (Y : ℤ → C)
    (t : ∀ p : ℤ, Y (p + 1) ⟶ Y p)
    (ht : ∀ p : ℤ, p ≤ 0 → IsIso (chainStep Y t p)) (p : ℤ) : Y p ⟶ Y 0 :=
  p.inductionOn' 0 (𝟙 _) (fun k _ i ↦ t k ≫ i)
    (fun k hk i ↦ by
      have := ht k hk
      exact inv (chainStep Y t k) ≫ i)

omit [Abelian C] in
private theorem chainMaps_succ (Y : ℤ → C)
    (t : ∀ p : ℤ, Y (p + 1) ⟶ Y p)
    (ht : ∀ p : ℤ, p ≤ 0 → IsIso (chainStep Y t p)) (p : ℤ) (hp : 0 ≤ p) :
    chainMaps Y t ht (p + 1) = t p ≫ chainMaps Y t ht p := by
  exact Int.inductionOn'_add_one hp

omit [Abelian C] in
private theorem chainMaps_pred (Y : ℤ → C)
    (t : ∀ p : ℤ, Y (p + 1) ⟶ Y p)
    (ht : ∀ p : ℤ, p ≤ 0 → IsIso (chainStep Y t p)) (p : ℤ) (hp : p ≤ 0) :
    chainMaps Y t ht (p - 1) =
      @inv _ _ _ _ (chainStep Y t p) (ht p hp) ≫ chainMaps Y t ht p := by
  exact Int.inductionOn'_sub_one hp

omit [Abelian C] in
private theorem chainMaps_zero (Y : ℤ → C)
    (t : ∀ p : ℤ, Y (p + 1) ⟶ Y p)
    (ht : ∀ p : ℤ, p ≤ 0 → IsIso (chainStep Y t p)) :
    chainMaps Y t ht 0 = 𝟙 _ := by
  exact Int.inductionOn'_self

omit [Abelian C] in
private theorem chainMaps_comm (Y : ℤ → C)
    (t : ∀ p : ℤ, Y (p + 1) ⟶ Y p)
    (ht : ∀ p : ℤ, p ≤ 0 → IsIso (chainStep Y t p)) (p : ℤ) :
    t p ≫ chainMaps Y t ht p = chainMaps Y t ht (p + 1) := by
  by_cases hp : 0 ≤ p
  · exact (chainMaps_succ Y t ht p hp).symm
  · have hk : p + 1 ≤ 0 := by omega
    have := ht (p + 1) hk
    have hc : chainStep Y t (p + 1) ≫ chainMaps Y t ht (p + 1 - 1) =
        chainMaps Y t ht (p + 1) := by
      rw [chainMaps_pred Y t ht (p + 1) hk]
      simp
    have he : (chainStep Y t (p + 1)) ≍ t p := by
      dsimp [chainStep]
      apply (eqToHom_comp_heq _ _).trans
      congr! 1
      omega
    have hi : chainMaps Y t ht (p + 1 - 1) ≍ chainMaps Y t ht p := by
      congr! 1
      omega
    have hec := heq_comp rfl (congrArg Y (show p + 1 - 1 = p by omega)) rfl he hi
    exact (eq_of_heq hec).symm.trans hc

omit [Abelian C] in
private theorem chainMaps_isIso (Y : ℤ → C)
    (t : ∀ p : ℤ, Y (p + 1) ⟶ Y p)
    (ht : ∀ p : ℤ, p ≤ 0 → IsIso (chainStep Y t p)) (p : ℤ) (hp : p ≤ 0) :
    IsIso (chainMaps Y t ht p) := by
  induction p using Int.induction_on with
  | zero => rw [chainMaps_zero]; infer_instance
  | succ k ih => omega
  | pred k ih =>
    have := ih (by omega)
    have := ht (- (k : ℤ)) (by omega)
    rw [chainMaps_pred Y t ht _ (by omega)]
    infer_instance

omit [Abelian C] in
private theorem chainMaps_factors (Y : ℤ → C)
    (t : ∀ p : ℤ, Y (p + 1) ⟶ Y p)
    (ht : ∀ p : ℤ, p ≤ 0 → IsIso (chainStep Y t p)) (T : C)
    (f : ∀ p : ℤ, Y p ⟶ T) (hf : ∀ p, t p ≫ f p = f (p + 1)) (p : ℤ) :
    chainMaps Y t ht p ≫ f 0 = f p := by
  have hstep (k : ℤ) : chainStep Y t k ≫ f (k - 1) = f k := by
    dsimp [chainStep]
    rw [Category.assoc, hf]
    simpa only [eqToHom_refl, Category.comp_id] using
      (eqToHom_naturality f (show k = k - 1 + 1 by omega)).symm
  induction p using Int.inductionOn' with
  | b => exact 0
  | zero => rw [chainMaps_zero, Category.id_comp]
  | succ k hk ih => rw [chainMaps_succ Y t ht k hk, Category.assoc, ih, hf]
  | pred k hk ih =>
    have := ht k hk
    rw [chainMaps_pred Y t ht k hk, Category.assoc, ih, ← hstep k]
    simp

/-- The diagonal colimits have the prescribed zeroth term and identity map there.
Their maps at nonpositive first index are isomorphisms.

Proof: for `p ≤ 0`, exactness gives `ker alpha = im f = 0`, since the source
of the relevant `f` has first index `p - 2 < 0`. It also gives
`im alpha = ker g = D`, since the target of the relevant `g` has first index
`p - 1 < 0`. Thus these diagonal transitions are isomorphisms. Set the colimit
object to `D 0 n` and its map at zero to the transported identity. For positive
first index compose the finitely many transitions down to zero. For negative
first index use the inverse of the finite composite from zero to that index.
The cocone equations follow by cancelling one transition in these composites.
A cocone to `T` factors through its map at zero: at positive indices iterate its
cocone equations, and at negative indices cancel the invertible transitions.
Uniqueness follows from the map at zero being the identity. The negative-index
maps are inverse composites of isomorphisms, proving the last assertion.
This construction is degreewise and needs no infinite colimits in `C`.
Source: blueprint thm-sp-half-plane-convergence, proof paragraph 1, stable diagonal;
Stacks Project, Tags 011Q and 011T.
(blueprint: lem-sp-half-plane-diagonal-colimits) -/
theorem halfPlane_diagonal_colimits (X : BigradedExactCouple C 0)
    (hE : ∀ p q : ℤ, p < 0 → IsZero (X.E p q)) :
    ∃ A : ∀ n : ℤ, AlphaColimit X n,
      ∃ hA : ∀ n : ℤ, (A n).obj = X.D 0 n,
        (∀ n : ℤ, (A n).ι 0 ≫ eqToHom (hA n) =
          eqToHom (by congr 1; omega)) ∧
        (∀ n p : ℤ, p ≤ 0 → IsIso ((A n).ι p)) := by
  let Y (n p : ℤ) := X.D p (n - p)
  have ht (n p : ℤ) (hp : p ≤ 0) :
      IsIso (chainStep (Y n) (X.alphaDiagonal n) p) := by
    have := alpha_iso_left X hE (p - 1 + 1) (n - (p - 1 + 1)) (by omega)
    dsimp [chainStep, alphaDiagonal]
    infer_instance
  let e (n : ℤ) : Y n 0 ≅ X.D 0 n := eqToIso (by dsimp [Y]; congr 1; omega)
  let A (n : ℤ) : AlphaColimit X n :=
    { obj := X.D 0 n
      ι := fun p ↦ chainMaps (Y n) (X.alphaDiagonal n) (ht n) p ≫
        (e n).hom
      comm := fun p ↦ by
        rw [← Category.assoc, chainMaps_comm (Y n) (X.alphaDiagonal n) (ht n)]
      isColimit := fun T f hf ↦ by
        let h : X.D 0 n ⟶ T := (e n).inv ≫ f 0
        refine ⟨h, ?_, ?_⟩
        · intro p
          dsimp [h]
          simp only [Category.assoc, Iso.hom_inv_id_assoc]
          exact chainMaps_factors (Y n) (X.alphaDiagonal n) (ht n) T f hf p
        · intro h' hh'
          have hh := hh' 0
          rw [chainMaps_zero, Category.id_comp] at hh
          apply (cancel_epi (e n).hom).1
          simpa [h] using hh }
  refine ⟨A, fun _ ↦ rfl, ?_, ?_⟩
  · intro n
    dsimp [A]
    rw [chainMaps_zero]
    simp only [Category.comp_id]
    exact Category.id_comp (e n).hom
  · intro n p hp
    have := chainMaps_isIso (Y n) (X.alphaDiagonal n) (ht n) p hp
    dsimp [A]
    infer_instance

end CategoryTheory.BigradedExactCouple

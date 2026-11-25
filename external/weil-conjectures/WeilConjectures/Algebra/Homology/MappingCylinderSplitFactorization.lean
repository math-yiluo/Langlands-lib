/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone

/-!
# Mapping-cylinder split factorization of a cochain map

Source: Stacks Project, Derived Categories, Lemma 013N, Definition 014G, and Remark 013O.
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

/-- A cochain map in an additive category factors through a termwise direct-summand inclusion
and a deformation retraction, preserving the specified upper bound and lowering the specified
lower bound by one. Source: Stacks Project, Lemma 013N, Definition 014G, and Remark 013O.

Proof (the six steps of the node):
1. Using finite biproducts (`def-weil-additive-category`), take
   `Tⁿ = Lⁿ ⊕ Kⁿ ⊕ Kⁿ⁺¹`, with differential matrix having rows
   `(d_L, 0, 0)`, `(0, d_K, id)`, and `(0, 0, -d_K)`.
   Matrix composition uses bilinearity (`def-weil-preadditive-category`).
2. Squaring this matrix gives zero: the diagonal entries are squares of differentials and
   the only additional entry is `d_K - d_K`.
3. Set `i = (α, id, 0)`, `p = (id, 0, 0)`, and `s = (id, 0, 0)` as a column.
   These commute with the differentials; their components give `i ≫ p = α` and `s ≫ p = id`.
4. In degree `n`, put `M = Lⁿ ⊕ Kⁿ⁺¹`. The isomorphism from `Kⁿ ⊕ M` to `Tⁿ` is
   `(k,l,k⁺) ↦ (α k + l,k,k⁺)`, with inverse `(l,k,k⁺) ↦ (k,l - α k,k⁺)`.
   Its first column is `i`, so the inverse carries `i` to the first biproduct inclusion.
5. The degree-minus-one map `(l,k,k⁺) ↦ (0,0,k)` gives `id - p ≫ s = dh + hd`.
   Negating it gives the homotopy from `p ≫ s` to `id` used below.
6. A finite biproduct of zero objects is zero. If the terms of `K` and `L` vanish below `n₀`,
   all three summands vanish below `n₀ - 1`; if they vanish above `n₁`, all three vanish above
   `n₁`. The same complex therefore preserves both bounds simultaneously. -/
theorem exists_mapping_cylinder_split_factorization
    {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
    {K L : CochainComplex C ℤ} (α : K ⟶ L) :
    ∃ (T : CochainComplex C ℤ) (i : K ⟶ T) (p : T ⟶ L) (s : L ⟶ T),
      i ≫ p = α ∧
      (∀ n : ℤ, ∃ (M : C) (e : T.X n ≅ K.X n ⊞ M), i.f n ≫ e.hom = biprod.inl) ∧
      s ≫ p = 𝟙 L ∧
      Nonempty (Homotopy (p ≫ s) (𝟙 T)) ∧
      (∀ n₀ : ℤ, (∀ n : ℤ, n < n₀ → IsZero (K.X n) ∧ IsZero (L.X n)) →
        ∀ n : ℤ, n < n₀ - 1 → IsZero (T.X n)) ∧
      (∀ n₁ : ℤ, (∀ n : ℤ, n₁ < n → IsZero (K.X n) ∧ IsZero (L.X n)) →
        ∀ n : ℤ, n₁ < n → IsZero (T.X n)) := by
  let Q := mappingCone (𝟙 K)
  let T := L ⊞ Q
  let i : K ⟶ T := biprod.lift α (mappingCone.inr (𝟙 K))
  let p : T ⟶ L := biprod.fst
  let s : L ⟶ T := biprod.inl
  have h₀ : Homotopy (𝟙 Q) 0 :=
    mappingCone.liftHomotopy _ _ _ (mappingCone.snd _) 0 (by simp) (by simp)
  have h₁ := (h₀.compRight (biprod.inr : Q ⟶ T)).compLeft (biprod.snd : T ⟶ Q)
  have h₂ := Homotopy.add (Homotopy.refl (p ≫ s)) h₁
  have ht : Homotopy (p ≫ s) (𝟙 T) := by
    refine (Homotopy.ofEq ?_).trans (h₂.symm.trans (Homotopy.ofEq ?_))
    · simp
    · simpa only [Category.id_comp, Category.comp_id] using
        (biprod.total (X := L) (Y := Q))
  let e₀ (n : ℤ) : T.X n ≅ L.X n ⊞ (K.X n ⊞ K.X (n + 1)) :=
    (HomologicalComplex.eval C (ComplexShape.up ℤ) n).mapBiprod L Q ≪≫
      biprod.mapIso (Iso.refl _) (HomologicalComplex.homotopyCofiber.XIsoBiprod
        (𝟙 K) n (n + 1) rfl ≪≫ biprod.braiding _ _)
  set_option backward.defeqAttrib.useBackward true in
  set_option backward.isDefEq.respectTransparency false in
  have hi₀ (n : ℤ) : i.f n ≫ (e₀ n).hom =
      biprod.lift (α.f n) (biprod.inl : K.X n ⟶ K.X n ⊞ K.X (n + 1)) := by
    change (HomologicalComplex.eval C (ComplexShape.up ℤ) n).map
      (biprod.lift α (mappingCone.inr (𝟙 K))) ≫
        ((HomologicalComplex.eval C (ComplexShape.up ℤ) n).mapBiprod L Q).hom ≫ _ = _
    rw [← Category.assoc, biprod.map_lift_mapBiprod]
    simp only [biprod.mapIso_hom, Iso.refl_hom, Iso.trans_hom]
    ext <;> simp [Q, mappingCone.inr, biprod.braiding, Category.assoc]
  refine ⟨T, i, p, s, by simp [i, p], ?_, by simp [s, p], ⟨ht⟩, ?_, ?_⟩
  · intro n
    let A := L.X n
    let B := K.X n
    let D := K.X (n + 1)
    let f : B ⟶ A := α.f n
    let e₁ : A ⊞ (B ⊞ D) ≅ B ⊞ (A ⊞ D) :=
      { hom := biprod.lift (biprod.snd ≫ biprod.fst)
          (biprod.lift (biprod.fst - biprod.snd ≫ biprod.fst ≫ f)
            (biprod.snd ≫ biprod.snd))
        inv := biprod.lift (biprod.fst ≫ f + biprod.snd ≫ biprod.fst)
          (biprod.lift biprod.fst (biprod.snd ≫ biprod.snd))
        hom_inv_id := by
          ext <;> simp [Category.assoc, Preadditive.comp_add]
        inv_hom_id := by
          ext <;> simp [Category.assoc, Preadditive.comp_sub] }
    refine ⟨A ⊞ D, e₀ n ≪≫ e₁, ?_⟩
    change i.f n ≫ (e₀ n).hom ≫ e₁.hom = _
    rw [← Category.assoc, hi₀]
    ext <;> simp [e₁, f, A, B, D, Category.assoc, Preadditive.comp_sub]
  · intro n₀ h n hn
    apply IsZero.of_iso _ (e₀ n)
    rw [biprod_isZero_iff, biprod_isZero_iff]
    exact ⟨(h n (by omega)).2, (h n (by omega)).1, (h (n + 1) (by omega)).1⟩
  · intro n₁ h n hn
    apply IsZero.of_iso _ (e₀ n)
    rw [biprod_isZero_iff, biprod_isZero_iff]
    exact ⟨(h n hn).2, (h n hn).1, (h (n + 1) (by omega)).1⟩

end CochainComplex

/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomologicalComplexBiprod

/-!
# The mapping cylinder factorization of a morphism of cochain complexes

Let `α : K ⟶ L` be a morphism of cochain complexes in an additive category. Put
`L' = L ⊞ mappingCone (𝟙 K)`. Then `α` factors as `K ⟶ L' ⟶ L` where the first map
`biprod.lift α (mappingCone.inr (𝟙 K))` is a termwise split injection and the second map
`biprod.fst` has the section `biprod.inl`, which is an inverse up to homotopy since
`mappingCone (𝟙 K)` is contractible. If `K` and `L` vanish in degrees `< n₀` (resp. `> n₁`), then
`L'` vanishes in degrees `< n₀ - 1` (resp. `> n₁`).
-/

@[expose] public section

open CategoryTheory Limits HomologicalComplex

namespace CochainComplex

variable {C : Type*} [Category* C] [Preadditive C] [HasBinaryBiproducts C]
  {K L : CochainComplex C ℤ} (α : K ⟶ L)

namespace mappingCylinderFactorization

/-- The middle complex `L ⊞ mappingCone (𝟙 K)` of the mapping cylinder factorization. -/
noncomputable abbrev obj : CochainComplex C ℤ := L ⊞ mappingCone (𝟙 K)

/-- The termwise split injection `K ⟶ L ⊞ mappingCone (𝟙 K)`. -/
noncomputable abbrev ι : K ⟶ obj (K := K) (L := L) :=
  biprod.lift α (mappingCone.inr (𝟙 K))

/-- The retraction `K.X n` of `(L ⊞ mappingCone (𝟙 K)).X n` onto the summand `K.X n`. -/
noncomputable abbrev retr (n : ℤ) : (obj (K := K) (L := L)).X n ⟶ K.X n :=
  (biprod.snd : obj (K := K) (L := L) ⟶ _).f n ≫ (mappingCone.snd (𝟙 K)).v n n (add_zero n)

/-- The projection of `(L ⊞ mappingCone (𝟙 K)).X n` onto the complement
`L.X n ⊞ K.X (n + 1)` of the summand `K.X n`. -/
noncomputable abbrev complProj (n : ℤ) :
    (obj (K := K) (L := L)).X n ⟶ L.X n ⊞ K.X (n + 1) :=
  biprod.lift ((biprod.fst : obj (K := K) (L := L) ⟶ _).f n - retr n ≫ α.f n)
    ((biprod.snd : obj (K := K) (L := L) ⟶ _).f n ≫ (mappingCone.fst (𝟙 K)).1.v n (n + 1) rfl)

/-- The inclusion of the complement `L.X n ⊞ K.X (n + 1)` into
`(L ⊞ mappingCone (𝟙 K)).X n`. -/
noncomputable abbrev complIncl (n : ℤ) :
    L.X n ⊞ K.X (n + 1) ⟶ (obj (K := K) (L := L)).X n :=
  biprod.desc ((biprod.inl : L ⟶ obj (K := K) (L := L)).f n)
    ((mappingCone.inl (𝟙 K)).v (n + 1) n (by lia) ≫
      (biprod.inr : _ ⟶ obj (K := K) (L := L)).f n)

set_option backward.isDefEq.respectTransparency false in
lemma total (n : ℤ) :
    retr n ≫ (ι α).f n + complProj α n ≫ complIncl n = 𝟙 _ := by
  have h₁ := congrArg (fun f => HomologicalComplex.Hom.f f n)
    (biprod.total : biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr =
      𝟙 (obj (K := K) (L := L)))
  have h₂ := mappingCone.id_X (𝟙 K) n (n + 1) rfl
  simp only [HomologicalComplex.add_f_apply, HomologicalComplex.comp_f,
    HomologicalComplex.id_f] at h₁
  have hι : (ι α).f n = α.f n ≫ (biprod.inl : L ⟶ obj (K := K) (L := L)).f n +
      (mappingCone.inr (𝟙 K)).f n ≫ (biprod.inr : _ ⟶ obj (K := K) (L := L)).f n := by
    simp [ι, biprod.lift_eq]
  rw [← h₁, hι]
  conv_rhs => rw [← Category.id_comp ((biprod.inr : _ ⟶ obj (K := K) (L := L)).f n), ← h₂]
  simp only [retr, complProj, complIncl, biprod.lift_desc, Preadditive.add_comp,
    Preadditive.comp_add, Preadditive.sub_comp, Category.assoc, ← HomologicalComplex.comp_f]
  abel

end mappingCylinderFactorization

open mappingCylinderFactorization in
/-- **Mapping cylinder factorization.** A morphism `α : K ⟶ L` of cochain complexes in an additive
category factors as `α = α' ≫ π` with `α'` a termwise split injection (in degree `n`, `α'` is
the inclusion of the summand `K.X n` of `L'.X n ≅ K.X n ⊞ M`) and `π : L' ⟶ L` having a section
`s` with `s ≫ π = 𝟙` and `π ≫ s` homotopic to `𝟙`. Moreover `L'` vanishes in degrees `< n₀ - 1`
(resp. `> n₁`) if `K` and `L` vanish in degrees `< n₀` (resp. `> n₁`).
(blueprint: `lem-weil-pbc-complex-mapping-cylinder-split-factorization`) -/
theorem exists_mappingCylinder_split_factorization :
    ∃ (L' : CochainComplex C ℤ) (α' : K ⟶ L') (π : L' ⟶ L) (s : L ⟶ L'),
      α' ≫ π = α ∧
      (∀ n : ℤ, ∃ (M : C) (e : L'.X n ≅ K.X n ⊞ M), α'.f n ≫ e.hom = biprod.inl) ∧
      s ≫ π = 𝟙 L ∧ Nonempty (Homotopy (π ≫ s) (𝟙 L')) ∧
      (∀ n₀ : ℤ, (∀ n < n₀, IsZero (K.X n) ∧ IsZero (L.X n)) →
        ∀ n < n₀ - 1, IsZero (L'.X n)) ∧
      (∀ n₁ : ℤ, (∀ n, n₁ < n → IsZero (K.X n) ∧ IsZero (L.X n)) →
        ∀ n, n₁ < n → IsZero (L'.X n)) := by
  have hzero (n : ℤ) (h : IsZero (K.X (n + 1)) ∧ IsZero (K.X n) ∧ IsZero (L.X n)) :
      IsZero ((obj (K := K) (L := L)).X n) := by
    refine IsZero.of_iso ?_ ((HomologicalComplex.eval C (ComplexShape.up ℤ) n).mapBiprod _ _)
    simp only [HomologicalComplex.eval_obj, biprod_isZero_iff, mappingCone.isZero_X_iff]
    exact ⟨h.2.2, h.1, h.2.1⟩
  refine ⟨obj (K := K) (L := L), ι α, biprod.fst, biprod.inl, by simp, fun n => ?_, by simp,
    ⟨?_⟩, fun n₀ h n hn => hzero n ⟨(h _ (by lia)).1, (h _ (by lia)).1, (h _ (by lia)).2⟩,
    fun n₁ h n hn => hzero n ⟨(h _ (by lia)).1, (h _ (by lia)).1, (h _ (by lia)).2⟩⟩
  · refine ⟨L.X n ⊞ K.X (n + 1),
      { hom := biprod.lift (retr n) (complProj α n)
        inv := biprod.desc ((ι α).f n) (complIncl n)
        hom_inv_id := by
          rw [biprod.lift_desc]
          exact total α n
        inv_hom_id := by
          ext <;> simp [← HomologicalComplex.comp_f] }, ?_⟩
    ext <;> simp [← HomologicalComplex.comp_f]
  · let h₀ : Homotopy (𝟙 (mappingCone (𝟙 K))) 0 :=
      mappingCone.liftHomotopy _ _ _ (mappingCone.snd _) 0 (by simp) (by simp)
    let h₁ := (h₀.compRight (biprod.inr : _ ⟶ obj (K := K) (L := L))).compLeft
      (biprod.snd : obj (K := K) (L := L) ⟶ _)
    let h₂ := Homotopy.add h₁ (Homotopy.refl (biprod.fst ≫ biprod.inl))
    exact (Homotopy.ofEq (by simp)).trans (h₂.symm.trans
      (Homotopy.ofEq (by rw [Category.id_comp, add_comm]; exact biprod.total)))

end CochainComplex

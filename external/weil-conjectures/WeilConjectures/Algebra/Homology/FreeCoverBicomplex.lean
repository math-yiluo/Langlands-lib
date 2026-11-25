/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits

import WeilConjectures.Algebra.Homology.FreeCoverColumns

/-!
# An exact bicomplex of free two-step covers

Source: Stacks Project, Tag 09KP, construction of the resolution and total augmentation.
(blueprint: lem-pc-derived-free-cover-bicomplex)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

private theorem totalAugmentation {A : Type u} [CommRing A]
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (K : HomologicalComplex₂ (ModuleCat.{u} A) (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    (a : K.X 0 ⟶ M) (hz : ∀ p : ℤ, 0 < p → IsZero (K.X p))
    (ha : K.d (-1) 0 ≫ a = 0) :
    ∃ ε : K.total (ComplexShape.up ℤ) ⟶ M,
      (∀ q : ℤ, K.ιTotal (ComplexShape.up ℤ) 0 q q (by simp) ≫ ε.f q = a.f q) ∧
      (∀ (p q n : ℤ) (_hp : p < 0)
        (h : ComplexShape.π (ComplexShape.up ℤ)
          (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n),
        K.ιTotal (ComplexShape.up ℤ) p q n h ≫ ε.f n = 0) := by
  classical
  let c (p q n : ℤ)
      (h : ComplexShape.π (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n) :
      (K.X p).X q ⟶ M.X n :=
    if hp : p = 0 then
      eqToHom (by
        subst p
        have hq : q = n := by simpa using h
        exact congrArg (fun i ↦ (K.X 0).X i) hq) ≫ a.f n
    else 0
  let f (n : ℤ) := K.totalDesc (fun p q h ↦ c p q n h)
  have hc0 (q : ℤ) : c 0 q q (by simp) = a.f q := by simp [c]
  have hcn (p q n : ℤ) (hp : p ≠ 0) (h) : c p q n h = 0 := by simp [c, hp]
  have comm (n m : ℤ) (hnm : (ComplexShape.up ℤ).Rel n m) :
      f n ≫ M.d n m = (K.total (ComplexShape.up ℤ)).d n m ≫ f m := by
    have hm : m = n + 1 := hnm.symm
    subst m
    apply HomologicalComplex₂.total.hom_ext
    intro p q h
    dsimp [f]
    rw [HomologicalComplex₂.ι_totalDesc_assoc]
    rw [HomologicalComplex₂.total_d, Preadditive.add_comp, Preadditive.comp_add]
    rw [← Category.assoc, HomologicalComplex₂.ι_D₁,
      ← Category.assoc, HomologicalComplex₂.ι_D₂]
    rw [K.d₁_eq (ComplexShape.up ℤ) (by rfl : (ComplexShape.up ℤ).Rel p (p + 1)) q (n + 1)
      (by dsimp at h ⊢; omega)]
    rw [K.d₂_eq (ComplexShape.up ℤ) p (by rfl : (ComplexShape.up ℤ).Rel q (q + 1)) (n + 1)
      (by dsimp at h ⊢; omega)]
    simp only [Linear.units_smul_comp, Category.assoc, HomologicalComplex₂.ι_totalDesc]
    by_cases hp : p = 0
    · subst p
      have hq : q = n := by simpa using h
      subst hq
      have hd : K.d 0 1 = 0 := (hz 1 (by omega)).eq_zero_of_tgt _
      simp [c, hd]
    · rw [hcn p q n hp h, zero_comp]
      by_cases hp1 : p + 1 = 0
      · have hp' : p = -1 := by omega
        subst p
        have hq : q = n + 1 := by dsimp at h; omega
        subst q
        have ha' := congrArg (fun t ↦ t.f (n + 1)) ha
        simp only [HomologicalComplex.comp_f, HomologicalComplex.zero_f] at ha'
        simp [c, ha']
      · simp [hcn, hp, hp1]
  refine ⟨{ f := f, comm' := comm }, ?_, ?_⟩
  · intro q
    exact (K.ι_totalDesc _ _ _ _).trans (hc0 q)
  · intro p q n hp h
    exact (K.ι_totalDesc _ _ _ _).trans (hcn p q n (by omega) h)

set_option linter.unusedVariables false in
/-- Iteration of the free-complex cover, followed by direct-sum totalization.
Source: Stacks Project, Differential Graded Algebra, Tag 09KP, proof, construction
of the resolution and its augmentation (using Tag 09KN).
(blueprint: lem-pc-derived-free-cover-bicomplex)

Proof. Starting at `N₀ = M`, choose the cover `Pᵢ → Nᵢ` of Tag 09KN and set
`Nᵢ₊₁` equal to its kernel. Define `Pᵢ₊₁ → Pᵢ` as the cover of `Nᵢ₊₁` followed
by the kernel inclusion. These maps compose to zero. They are exact in each
module degree since the covers are surjective and their kernels are the chosen
`Nᵢ₊₁`. They are also exact on cycles: a cycle mapping to zero factors uniquely
through the kernel complex, is a cycle there since its inclusion is injective,
and lifts to a cycle of the next cover by the cocycle-surjectivity clause of 09KN.
The same argument proves exactness at `P₀`, and 09KN gives surjectivity of both
augmented rows at `M`.

Put `Pᵢ` in column `-i`, and zero in positive columns. The horizontal maps are
the maps just constructed; they commute with the vertical differentials because
they are maps of complexes. This gives `K`. Module categories have the direct
sums defining its total complex. On each diagonal define the augmentation by
the cover `P₀ → M` on column zero and zero on negative columns. The horizontal
boundary from column `-1` is killed by this cover; in column zero the vertical
sign is one. Thus these component maps commute with differentials and give `ε`.
Finally retain the split short exact sequence and the two free graded pieces
provided by 09KN for each `Pᵢ`; their middle objects identify with `K.X (-i)`.
-/
theorem exists_freeCoverBicomplex {A : Type u} [CommRing A]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    ∃ K : HomologicalComplex₂ (ModuleCat.{u} A) (ComplexShape.up ℤ) (ComplexShape.up ℤ),
      ∃ (ε : K.total (ComplexShape.up ℤ) ⟶ M) (a : K.X 0 ⟶ M),
        (∀ p : ℤ, 0 < p → IsZero (K.X p)) ∧
        (∀ q : ℤ, K.ιTotal (ComplexShape.up ℤ) 0 q q (by simp) ≫ ε.f q = a.f q) ∧
        (∀ (p q n : ℤ) (hp : p < 0)
          (h : ComplexShape.π (ComplexShape.up ℤ)
            (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n),
          K.ιTotal (ComplexShape.up ℤ) p q n h ≫ ε.f n = 0) ∧
        (∀ (p q : ℤ), p < -1 →
          Function.Exact ((K.d p (p + 1)).f q).hom ((K.d (p + 1) (p + 2)).f q).hom) ∧
        (∀ q : ℤ, Function.Exact ((K.d (-1) 0).f q).hom (a.f q).hom) ∧
        (∀ q : ℤ, Function.Surjective (a.f q).hom) ∧
        (∀ (p q : ℤ), p < -1 →
          Function.Exact (HomologicalComplex.cyclesMap (K.d p (p + 1)) q).hom
            (HomologicalComplex.cyclesMap (K.d (p + 1) (p + 2)) q).hom) ∧
        (∀ q : ℤ, Function.Exact (HomologicalComplex.cyclesMap (K.d (-1) 0) q).hom
          (HomologicalComplex.cyclesMap a q).hom) ∧
        (∀ q : ℤ, Function.Surjective (HomologicalComplex.cyclesMap a q).hom) ∧
        (∀ p : ℤ, p ≤ 0 →
      ∃ S : ShortComplex (CochainComplex (ModuleCat.{u} A) ℤ),
        Nonempty (S.X₂ ≅ K.X p) ∧ S.ShortExact ∧
        (∀ k : ℤ,
          Nonempty
            (S.map (HomologicalComplex.eval (ModuleCat.{u} A) (ComplexShape.up ℤ) k)).Splitting) ∧
        ∃ (I₁ I₃ : Type u) (d₁ : I₁ → ℤ) (d₃ : I₃ → ℤ),
          Nonempty (S.X₁ ≅ ∐ (fun i : I₁ ↦
            (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) (d₁ i)).obj
              (ModuleCat.of A A))) ∧
          Nonempty (S.X₃ ≅ ∐ (fun i : I₃ ↦
            (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) (d₃ i)).obj
              (ModuleCat.of A A)))) := by
  obtain ⟨K, a, hz, hterms, hterms₀, hsurj, hcycles, hcycles₀, hcyclesSurj, hcols⟩ :=
    exists_freeCoverColumns M
  have ha : K.d (-1) 0 ≫ a = 0 := by
    ext q x
    exact (hterms₀ q).apply_apply_eq_zero x
  obtain ⟨ε, hzero, hneg⟩ := totalAugmentation M K a hz ha
  exact ⟨K, ε, a, hz, hzero, hneg, hterms, hterms₀, hsurj,
    hcycles, hcycles₀, hcyclesSurj, hcols⟩

end CochainComplex

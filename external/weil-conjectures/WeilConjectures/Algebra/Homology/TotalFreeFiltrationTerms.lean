/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits

/-!
# Concrete terms of the alternating column filtration

Source: Stacks Project, Tag 09KP, filtration construction.
(blueprint: lem-pc-derived-total-filtration-stable)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex
namespace TotalFreeFiltration

variable {A : Type u} [CommRing A]
variable (K : HomologicalComplex₂ (ModuleCat.{u} A) (ComplexShape.up ℤ) (ComplexShape.up ℤ))
variable (S : ℕ → ShortComplex (CochainComplex (ModuleCat.{u} A) ℤ))
variable (e : ∀ j : ℕ, (S j).X₂ ≅ K.X (-(j : ℤ)))

/-- The inclusion of the full column `-j` into total degree `k`.
Source: Stacks Project, Tag 09KP, proof. 
(blueprint: lem-pc-derived-total-filtration-stable)
-/
noncomputable def full (j : ℕ) (k : ℤ) :
    (K.X (-(j : ℤ))).X (k + j) ⟶ (K.total (ComplexShape.up ℤ)).X k :=
  K.ιTotal (ComplexShape.up ℤ) (-(j : ℤ)) (k + j) k (by simp)

/-- The inclusion of the lower column piece into total degree `k`.
Source: Stacks Project, Tag 09KP, proof. 
(blueprint: lem-pc-derived-total-filtration-stable)
-/
noncomputable def lower (j : ℕ) (k : ℤ) :
    (S j).X₁.X (k + j) ⟶ (K.total (ComplexShape.up ℤ)).X k :=
  (S j).f.f (k + j) ≫ (e j).hom.f (k + j) ≫ full K j k

/-- The actual submodule defining stage `n` in degree `k`: full columns enter at
`2*j+2`, their lower pieces at `2*j+1`. Source: Stacks Project, Tag 09KP, proof.
(blueprint: lem-pc-derived-total-filtration-stable) -/
noncomputable def term (n : ℕ) (k : ℤ) :
    Submodule A ((K.total (ComplexShape.up ℤ)).X k) :=
  ⨆ j : ℕ, (if 2 * j + 2 ≤ n then LinearMap.range (full K j k).hom else ⊥) ⊔
    (if 2 * j + 1 ≤ n then LinearMap.range (lower K S e j k).hom else ⊥)

/-- (blueprint: lem-pc-derived-total-filtration-stable) -/
lemma term_zero (k : ℤ) : term K S e 0 k = ⊥ := by
  simp [term]

/-- (blueprint: lem-pc-derived-total-filtration-stable) -/
lemma term_mono {n m : ℕ} (h : n ≤ m) (k : ℤ) :
    term K S e n k ≤ term K S e m k := by
  apply iSup_mono
  intro j
  apply sup_le_sup
  · split_ifs <;> first | exact le_rfl | exact bot_le | omega
  · split_ifs <;> first | exact le_rfl | exact bot_le | omega

private lemma full_mem (n j : ℕ) (k : ℤ) (h : 2 * j + 2 ≤ n)
    (x : (K.X (-(j : ℤ))).X (k + j)) : full K j k x ∈ term K S e n k := by
  apply (le_iSup (fun j : ℕ ↦
    (if 2 * j + 2 ≤ n then LinearMap.range (full K j k).hom else ⊥) ⊔
      (if 2 * j + 1 ≤ n then LinearMap.range (lower K S e j k).hom else ⊥)) j)
  apply Submodule.mem_sup_left
  simpa only [ite_eq_left h] using (LinearMap.mem_range_self (full K j k).hom x)

private lemma lower_mem (n j : ℕ) (k : ℤ) (h : 2 * j + 1 ≤ n)
    (x : (S j).X₁.X (k + j)) : lower K S e j k x ∈ term K S e n k := by
  apply (le_iSup (fun j : ℕ ↦
    (if 2 * j + 2 ≤ n then LinearMap.range (full K j k).hom else ⊥) ⊔
      (if 2 * j + 1 ≤ n then LinearMap.range (lower K S e j k).hom else ⊥)) j)
  apply Submodule.mem_sup_right
  simpa only [ite_eq_left h] using (LinearMap.mem_range_self (lower K S e j k).hom x)

private lemma full_d (j : ℕ) (k : ℤ) :
    full K j k ≫ (K.total (ComplexShape.up ℤ)).d k (k + 1) =
      (K.d (-(j : ℤ)) (-(j : ℤ) + 1)).f (k + j) ≫
        K.ιTotal (ComplexShape.up ℤ) (-(j : ℤ) + 1) (k + j) (k + 1) (by dsimp; omega) +
      ComplexShape.ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (-(j : ℤ), k + j) •
        ((K.X (-(j : ℤ))).d (k + j) (k + 1 + j) ≫ full K j (k + 1)) := by
  dsimp only [full]
  rw [HomologicalComplex₂.total_d, Preadditive.comp_add,
    HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂]
  rw [K.d₁_eq (ComplexShape.up ℤ) (by rfl) (k + j) (k + 1) (by dsimp; omega)]
  rw [K.d₂_eq (ComplexShape.up ℤ) (-(j : ℤ))
    (show (ComplexShape.up ℤ).Rel (k + j) (k + 1 + j) from by change k + j + 1 = k + 1 + j; omega)
    (k + 1) (by dsimp; omega)]
  simp

private lemma horizontal_mem
    (hp : ∀ p : ℤ, 0 < p → IsZero (K.X p)) (n j : ℕ) (k : ℤ)
    (h : 2 * j + 1 ≤ n) (x : (K.X (-(j : ℤ))).X (k + j)) :
    (K.ιTotal (ComplexShape.up ℤ) (-(j : ℤ) + 1) (k + j) (k + 1)
      (by dsimp; omega)) ((K.d (-(j : ℤ)) (-(j : ℤ) + 1)).f (k + j) x) ∈
        term K S e n (k + 1) := by
  cases j with
  | zero =>
    have hd : K.d 0 1 = 0 := (hp 1 (by omega)).eq_zero_of_tgt _
    simp [hd]
  | succ j =>
    have hj : -(↑(j + 1) : ℤ) + 1 = -(j : ℤ) := by push_cast; omega
    have hk : k + (↑(j + 1) : ℤ) = k + 1 + j := by push_cast; omega
    generalize (K.d (-(↑(j + 1) : ℤ)) (-(↑(j + 1) : ℤ) + 1)).f
      (k + ↑(j + 1)) x = y
    have hi := congrArg (fun f ↦ f y)
      (K.XXIsoOfEq_hom_ιTotal (ComplexShape.up ℤ) hj hk (k + 1) (by simp))
    rw [← hi]
    exact full_mem K S e n j (k + 1) (by omega) _

private lemma full_d_mem
    (hp : ∀ p : ℤ, 0 < p → IsZero (K.X p)) (n j : ℕ) (k : ℤ)
    (h : 2 * j + 2 ≤ n) (x : (K.X (-(j : ℤ))).X (k + j)) :
    (K.total (ComplexShape.up ℤ)).d k (k + 1) (full K j k x) ∈
      term K S e n (k + 1) := by
  have hd := congrArg (fun f ↦ f x) (full_d K j k)
  simp only [Units.smul_def] at hd
  change (K.total (ComplexShape.up ℤ)).d k (k + 1) (full K j k x) =
    _ + (_ : ℤ) • (full K j (k + 1)
      ((K.X (-(j : ℤ))).d (k + j) (k + 1 + j) x)) at hd
  rw [hd]
  apply Submodule.add_mem
  · exact horizontal_mem K S e hp n j k (by omega) x
  · exact (term K S e n (k + 1)).toAddSubgroup.zsmul_mem
      (full_mem K S e n j (k + 1) h _) _

private lemma lower_d_mem
    (hp : ∀ p : ℤ, 0 < p → IsZero (K.X p)) (n j : ℕ) (k : ℤ)
    (h : 2 * j + 1 ≤ n) (x : (S j).X₁.X (k + j)) :
    (K.total (ComplexShape.up ℤ)).d k (k + 1) (lower K S e j k x) ∈
      term K S e n (k + 1) := by
  let a : (S j).X₁ ⟶ K.X (-(j : ℤ)) := (S j).f ≫ (e j).hom
  have hd := congrArg (fun f ↦ f (a.f (k + j) x)) (full_d K j k)
  simp only [Units.smul_def] at hd
  change (K.total (ComplexShape.up ℤ)).d k (k + 1) (lower K S e j k x) =
    _ + (_ : ℤ) • (full K j (k + 1)
      ((K.X (-(j : ℤ))).d (k + j) (k + 1 + j) (a.f (k + j) x))) at hd
  rw [hd]
  apply Submodule.add_mem
  · exact horizontal_mem K S e hp n j k h _
  · have hc := congrArg (fun f ↦ f x) (a.comm (k + j) (k + 1 + j))
    change (K.X (-(j : ℤ))).d (k + j) (k + 1 + j) (a.f (k + j) x) =
      a.f (k + 1 + j) ((S j).X₁.d (k + j) (k + 1 + j) x) at hc
    rw [hc]
    exact (term K S e n (k + 1)).toAddSubgroup.zsmul_mem
      (lower_mem K S e n j (k + 1) h _) _

/-- The alternating column submodules are preserved by the total differential.
Source: Stacks Project, Tag 09KP, proof, filtration construction.
(blueprint: lem-pc-derived-total-filtration-stable)

Proof. It suffices to check the generators in each range defining `term`.
For a full-column generator the vertical differential remains in that column,
while the horizontal differential goes from `-j` to `-(j-1)`. For `j>0`, that
full column entered two stages earlier. For `j=0`, its target column is positive
and zero by the hypothesis. For a lower-piece generator the vertical differential
remains in the lower piece, because the composite of the short-complex arrow and
`e.hom` is a cochain map. Its horizontal differential lands in the earlier full
column, with the same zero-column exception at `j=0`. Both summands of the total
differential therefore lie in the target submodule. Closure under addition and
scalar multiplication extends the calculation to the suprema of ranges.
-/
theorem differential_mem
    (h_positive : ∀ p : ℤ, 0 < p → IsZero (K.X p))
    (n : ℕ) (k l : ℤ) (x : (K.total (ComplexShape.up ℤ)).X k)
    (hx : x ∈ term K S e n k) :
    (K.total (ComplexShape.up ℤ)).d k l x ∈ term K S e n l := by
  classical
  by_cases hkl : (ComplexShape.up ℤ).Rel k l
  · have hl : l = k + 1 := hkl.symm
    subst l
    suffices hs : term K S e n k ≤
        (term K S e n (k + 1)).comap
          ((K.total (ComplexShape.up ℤ)).d k (k + 1)).hom from hs hx
    apply iSup_le
    intro j
    apply sup_le
    · split_ifs with hj
      · rintro y ⟨z, rfl⟩
        exact full_d_mem K S e h_positive n j k hj z
      · exact bot_le
    · split_ifs with hj
      · rintro y ⟨z, rfl⟩
        exact lower_d_mem K S e h_positive n j k hj z
      · exact bot_le
  · rw [HomologicalComplex.shape _ k l hkl]
    exact (term K S e n l).zero_mem

/-- Restriction of a module complex to differential-stable submodules.
Source: Stacks Project, Tag 09KP, proof. 
(blueprint: lem-pc-derived-total-filtration-stable)
-/
noncomputable def restrictComplex (T : CochainComplex (ModuleCat.{u} A) ℤ)
    (M : ∀ k : ℤ, Submodule A (T.X k))
    (h : ∀ k l (x : T.X k), x ∈ M k → T.d k l x ∈ M l) :
    CochainComplex (ModuleCat.{u} A) ℤ where
  X k := ModuleCat.of A (M k)
  d k l := ModuleCat.ofHom
    (((T.d k l).hom.comp (M k).subtype).codRestrict (M l)
      (fun x ↦ h k l x x.property))
  shape k l hk := by
    ext x
    change T.d k l x.val = 0
    rw [HomologicalComplex.shape _ k l hk]
    rfl
  d_comp_d' k l m _ _ := by
    ext x
    change T.d l m (T.d k l x.val) = 0
    exact congrArg (fun f ↦ f x.val) (T.d_comp_d k l m)

/-- Inclusion from a restricted complex.
Source: Stacks Project, Tag 09KP, proof. 
(blueprint: lem-pc-derived-total-filtration-stable)
-/
noncomputable def restrictInclusion (T : CochainComplex (ModuleCat.{u} A) ℤ)
    (M : ∀ k : ℤ, Submodule A (T.X k))
    (h : ∀ k l (x : T.X k), x ∈ M k → T.d k l x ∈ M l) :
    restrictComplex T M h ⟶ T where
  f k := ModuleCat.ofHom (M k).subtype
  comm' k l _ := by ext x; rfl

/-- Inclusion for two nested differential-stable submodule families.
Source: Stacks Project, Tag 09KP, proof. 
(blueprint: lem-pc-derived-total-filtration-stable)
-/
noncomputable def restrictMap (T : CochainComplex (ModuleCat.{u} A) ℤ)
    (M N : ∀ k : ℤ, Submodule A (T.X k))
    (hM : ∀ k l (x : T.X k), x ∈ M k → T.d k l x ∈ M l)
    (hN : ∀ k l (x : T.X k), x ∈ N k → T.d k l x ∈ N l)
    (hMN : ∀ k, M k ≤ N k) : restrictComplex T M hM ⟶ restrictComplex T N hN where
  f k := ModuleCat.ofHom (Submodule.inclusion (hMN k))
  comm' k l _ := by ext x; rfl

/-- (blueprint: lem-pc-derived-total-filtration-stable) -/
lemma restrict_zero (T : CochainComplex (ModuleCat.{u} A) ℤ)
    (M : ∀ k : ℤ, Submodule A (T.X k))
    (h : ∀ k l (x : T.X k), x ∈ M k → T.d k l x ∈ M l)
    (h0 : ∀ k, M k = ⊥) : IsZero (restrictComplex T M h) := by
  rw [IsZero.iff_id_eq_zero]
  ext k x
  apply Subtype.ext
  exact (Submodule.mem_bot A).mp ((h0 k) ▸ x.property)

/-- (blueprint: lem-pc-derived-total-filtration-stable) -/
lemma restrict_mono (T : CochainComplex (ModuleCat.{u} A) ℤ)
    (M : ∀ k : ℤ, Submodule A (T.X k))
    (h : ∀ k l (x : T.X k), x ∈ M k → T.d k l x ∈ M l) :
    Mono (restrictInclusion T M h) := by
  apply HomologicalComplex.mono_of_mono_f
  intro k
  apply (ModuleCat.mono_iff_injective _).mpr
  exact Subtype.val_injective

/-- (blueprint: lem-pc-derived-total-filtration-stable) -/
lemma restrict_comp (T : CochainComplex (ModuleCat.{u} A) ℤ)
    (M N : ∀ k : ℤ, Submodule A (T.X k))
    (hM : ∀ k l (x : T.X k), x ∈ M k → T.d k l x ∈ M l)
    (hN : ∀ k l (x : T.X k), x ∈ N k → T.d k l x ∈ N l)
    (hMN : ∀ k, M k ≤ N k) :
    restrictMap T M N hM hN hMN ≫ restrictInclusion T N hN =
      restrictInclusion T M hM := by
  ext k x
  rfl

/-- (blueprint: lem-pc-derived-total-filtration-stable) -/
lemma restrict_surjective (T : CochainComplex (ModuleCat.{u} A) ℤ)
    (M : ℕ → ∀ k : ℤ, Submodule A (T.X k))
    (h : ∀ n k l (x : T.X k), x ∈ M n k → T.d k l x ∈ M n l)
    (he : ∀ k (x : T.X k), ∃ n, x ∈ M n k) (k : ℤ) (x : T.X k) :
    ∃ (n : ℕ) (y : (restrictComplex T (M n) (h n)).X k),
      (restrictInclusion T (M n) (h n)).f k y = x := by
  obtain ⟨n, hx⟩ := he k x
  exact ⟨n, ⟨x, hx⟩, rfl⟩

variable (h_positive : ∀ p : ℤ, 0 < p → IsZero (K.X p))

/-- Restrict the total differential to the explicitly constructed submodules.
Source: Stacks Project, Tag 09KP, proof. 
(blueprint: lem-pc-derived-total-filtration-stable)
-/
noncomputable def complex (n : ℕ) : CochainComplex (ModuleCat.{u} A) ℤ :=
  restrictComplex (K.total (ComplexShape.up ℤ)) (term K S e n)
    (differential_mem K S e h_positive n)

/-- Inclusion of a constructed stage into the total complex.
Source: Stacks Project, Tag 09KP, proof. 
(blueprint: lem-pc-derived-total-filtration-stable)
-/
noncomputable def inclusion (n : ℕ) : complex K S e h_positive n ⟶
    K.total (ComplexShape.up ℤ) :=
  restrictInclusion (K.total (ComplexShape.up ℤ)) (term K S e n)
    (differential_mem K S e h_positive n)

/-- Successive inclusion between constructed stages.
Source: Stacks Project, Tag 09KP, proof. 
(blueprint: lem-pc-derived-total-filtration-stable)
-/
noncomputable def step (n : ℕ) : complex K S e h_positive n ⟶
    complex K S e h_positive (n + 1) :=
  restrictMap (K.total (ComplexShape.up ℤ)) (term K S e n) (term K S e (n + 1))
    (differential_mem K S e h_positive n) (differential_mem K S e h_positive (n + 1))
    (fun k ↦ term_mono K S e (Nat.le_succ n) k)

end TotalFreeFiltration
end CochainComplex

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.TotalFreeFiltrationTerms
import Mathlib.Algebra.Module.Submodule.EqLocus

/-!
# Degreewise retractions of the alternating column filtration

Source: Stacks Project, Tag 09KP, filtration construction.
(blueprint: lem-pc-derived-total-filtration-step-retraction)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex.TotalFreeFiltration

variable {A : Type u} [CommRing A]
variable (K : HomologicalComplex₂ (ModuleCat.{u} A) (ComplexShape.up ℤ) (ComplexShape.up ℤ))
variable (S : ℕ → ShortComplex (CochainComplex (ModuleCat.{u} A) ℤ))
variable (e : ∀ j : ℕ, (S j).X₂ ≅ K.X (-(j : ℤ)))
variable (h_positive : ∀ p : ℤ, 0 < p → IsZero (K.X p))

/-- Each filtration inclusion has a left inverse in each degree.
Source: Stacks Project, Tag 09KP, alternating column filtration.
(blueprint: lem-pc-derived-total-filtration-step-retraction)

Proof. Decompose the total module in degree k as the coproduct of its column
terms. At stage 2j the submodule is the sum of full columns -i for i<j;
at stage 2j+1 it also includes the image of the first arrow of S j.
Projection onto the preceding full columns retracts the even inclusion.
For the odd inclusion, project onto the preceding columns and apply the
retraction of the first arrow supplied by the splitting of S j in degree k+j,
transported through e j. Directness of the column summands proves that these
maps restrict to the indicated submodules and compose with the inclusions to
identity. Every n is even or odd. For j=0 the preceding sum is zero, so the
same constructions apply. No exactness or freeness hypothesis is needed. -/
theorem step_retraction
    (h_split : ∀ j (k : ℤ), Nonempty
      ((S j).map (HomologicalComplex.eval (ModuleCat.{u} A) (ComplexShape.up ℤ) k)).Splitting)
    (n : ℕ) (k : ℤ) :
    ∃ r : (complex K S e h_positive (n + 1)).X k ⟶
      (complex K S e h_positive n).X k,
      (step K S e h_positive n).f k ≫ r =
        𝟙 ((complex K S e h_positive n).X k) := by
  classical
  change ∃ r : ModuleCat.of A (term K S e (n + 1) k) ⟶
    ModuleCat.of A (term K S e n k),
    ModuleCat.ofHom (Submodule.inclusion (term_mono K S e (Nat.le_succ n) k)) ≫ r = 𝟙 _
  let M := term K S e n k
  let ι : ModuleCat.of A M ⟶ (K.total (ComplexShape.up ℤ)).X k :=
    ModuleCat.ofHom M.subtype
  have finish (V : ModuleCat.{u} A) (P Q : Submodule A V) (hPQ : P ≤ Q)
      (r : V ⟶ ModuleCat.of A P)
      (hf : P ≤ LinearMap.eqLocus (r ≫ ModuleCat.ofHom P.subtype).hom LinearMap.id) :
      ∃ t : ModuleCat.of A Q ⟶ ModuleCat.of A P,
        ModuleCat.ofHom (Submodule.inclusion hPQ) ≫ t = 𝟙 (ModuleCat.of A P) := by
    refine ⟨ModuleCat.ofHom (r.hom.comp Q.subtype), ?_⟩
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact hf x.property
  have hfull (j : ℕ) (hj : 2 * j + 2 ≤ n) (x : (K.X (-(j : ℤ))).X (k + j)) :
      full K j k x ∈ M := by
    apply (le_iSup (fun j' : ℕ ↦
      (if 2 * j' + 2 ≤ n then LinearMap.range (full K j' k).hom else ⊥) ⊔
      (if 2 * j' + 1 ≤ n then LinearMap.range (lower K S e j' k).hom else ⊥)) j)
    apply Submodule.mem_sup_left
    simp only [ite_eq_left hj]
    exact ⟨x, rfl⟩
  have hlower (j : ℕ) (hj : 2 * j + 1 ≤ n) (x : (S j).X₁.X (k + j)) :
      lower K S e j k x ∈ M := by
    apply (le_iSup (fun j' : ℕ ↦
      (if 2 * j' + 2 ≤ n then LinearMap.range (full K j' k).hom else ⊥) ⊔
      (if 2 * j' + 1 ≤ n then LinearMap.range (lower K S e j' k).hom else ⊥)) j)
    apply Submodule.mem_sup_right
    simp only [ite_eq_left hj]
    exact ⟨x, rfl⟩
  have σ : ∀ j : ℕ,
      ((S j).map (HomologicalComplex.eval (ModuleCat.{u} A) (ComplexShape.up ℤ)
        (k + j))).Splitting := fun j ↦ (h_split j (k + j)).some
  let g (j : ℕ) : (K.X (-(j : ℤ))).X (k + j) ⟶ ModuleCat.of A M :=
    if hj : 2 * j + 2 ≤ n then
      ModuleCat.ofHom ((full K j k).hom.codRestrict M (hfull j hj))
    else if hj : 2 * j + 1 ≤ n then
      (e j).inv.f (k + j) ≫ (σ j).r ≫
        ModuleCat.ofHom ((lower K S e j k).hom.codRestrict M (hlower j hj))
    else 0
  let f : ∀ p q (_hi : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (p, q) = k), (K.X p).X q ⟶ ModuleCat.of A M :=
    fun p q hi ↦ by
      by_cases hp : p ≤ 0
      · have hpj : p = -(((-p).toNat : ℕ) : ℤ) := by
          rw [Int.toNat_of_nonneg (by omega)]
          omega
        have hq : q = k + ((-p).toNat : ℕ) := by
          change p + q = k at hi
          rw [Int.toNat_of_nonneg (by omega)]
          omega
        exact (K.XXIsoOfEq _ _ _ hpj hq).hom ≫ g (-p).toNat
      · exact 0
  let r := K.totalDesc f
  have hg (j l : ℕ) (hl : l = j) (h₁ : -(j : ℤ) = -(l : ℤ))
      (h₂ : k + (j : ℤ) = k + (l : ℤ)) :
      (K.XXIsoOfEq _ _ _ h₁ h₂).hom ≫ g l = g j := by
    subst l
    simp only [HomologicalComplex₂.XXIsoOfEq_rfl, Iso.refl_hom, Category.id_comp]
  have hfg (j : ℕ) : full K j k ≫ r = g j := by
    change K.ιTotal (ComplexShape.up ℤ) (-(j : ℤ)) (k + j) k _ ≫
      K.totalDesc f = g j
    rw [HomologicalComplex₂.ι_totalDesc]
    dsimp only [f]
    rw [dite_eq_left (neg_nonpos.mpr (Int.natCast_nonneg j))]
    exact hg j _ (by simp) _ _
  have hfix_full (j : ℕ) (hj : 2 * j + 2 ≤ n) :
      full K j k ≫ r ≫ ι = full K j k := by
    rw [← Category.assoc, hfg]
    simp only [g, dite_eq_left hj]
    rfl
  have hfix_lower (j : ℕ) (hj : 2 * j + 1 ≤ n) :
      lower K S e j k ≫ r ≫ ι = lower K S e j k := by
    change ((S j).f.f (k + j) ≫ (e j).hom.f (k + j) ≫ full K j k) ≫ r ≫ ι =
      (S j).f.f (k + j) ≫ (e j).hom.f (k + j) ≫ full K j k
    simp only [← Category.assoc]
    rw [Category.assoc _ (full K j k) r, hfg]
    by_cases hj' : 2 * j + 2 ≤ n
    · simp only [g, dite_eq_left hj']
      rfl
    · simp only [g, dite_eq_right hj', dite_eq_left hj]
      have he : (e j).hom.f (k + j) ≫ (e j).inv.f (k + j) = 𝟙 _ :=
        HomologicalComplex.congr_hom (e j).hom_inv_id (k + j)
      have hs : (S j).f.f (k + j) ≫ (σ j).r = 𝟙 _ := (σ j).f_r
      simp only [Category.assoc]
      rw [← Category.assoc ((e j).hom.f (k + j)), he, Category.id_comp,
        ← Category.assoc ((S j).f.f (k + j)), hs, Category.id_comp]
      rfl
  have hfix : M ≤ LinearMap.eqLocus (r ≫ ι).hom LinearMap.id := by
    apply iSup_le
    intro j
    apply sup_le
    · split_ifs with hj
      · rintro x ⟨y, rfl⟩
        exact congrArg (fun a ↦ a y) (hfix_full j hj)
      · exact bot_le
    · split_ifs with hj
      · rintro x ⟨y, rfl⟩
        exact congrArg (fun a ↦ a y) (hfix_lower j hj)
      · exact bot_le
  exact finish _ M (term K S e (n + 1) k)
    (term_mono K S e (Nat.le_succ n) k) r hfix

end CochainComplex.TotalFreeFiltration

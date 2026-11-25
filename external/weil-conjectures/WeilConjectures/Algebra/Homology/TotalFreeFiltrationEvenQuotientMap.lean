/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.TotalFreeFiltrationTerms
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift

/-!
# The canonical degree maps into the even column quotient

Source: Stacks Project, Tag 09KP, alternating column filtration.
(blueprint: lem-pc-derived-total-filtration-even-quotient-map)
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex.TotalFreeFiltration

variable {A : Type u} [CommRing A]
variable (K : HomologicalComplex₂ (ModuleCat.{u} A) (ComplexShape.up ℤ) (ComplexShape.up ℤ))
variable (S : ℕ → ShortComplex (CochainComplex (ModuleCat.{u} A) ℤ))
variable (e : ∀ j : ℕ, (S j).X₂ ≅ K.X (-(j : ℤ)))
variable (h_positive : ∀ p : ℤ, 0 < p → IsZero (K.X p))

/-- The lower column map has image in the odd filtration term.
Source: Stacks Project, Tag 09KP, definition of the alternating filtration. -/
lemma lower_mem_odd (j : ℕ) (k : ℤ) (x : (S j).X₁.X (k + j)) :
    lower K S e j k x ∈ term K S e (2 * j + 1) k := by
  apply (le_iSup (fun a : ℕ ↦
    (if 2 * a + 2 ≤ 2 * j + 1 then LinearMap.range (full K a k).hom else ⊥) ⊔
      (if 2 * a + 1 ≤ 2 * j + 1 then LinearMap.range (lower K S e a k).hom else ⊥)) j)
  apply (le_sup_right :
    (if 2 * j + 1 ≤ 2 * j + 1 then LinearMap.range (lower K S e j k).hom else ⊥) ≤ _)
  simp only [le_refl, ite_true]
  exact ⟨x, rfl⟩

/-- The explicit lower-column map, with its codomain restricted to the odd term.
Source: Stacks Project, Tag 09KP, alternating column filtration. -/
noncomputable def lowerToOdd (j : ℕ) (k : ℤ) :
    (S j).X₁.X (k + j) ⟶ (complex K S e h_positive (2 * j + 1)).X k :=
  ModuleCat.ofHom ((lower K S e j k).hom.codRestrict
    (term K S e (2 * j + 1) k) (lower_mem_odd K S e j k))

/-- The canonical degree map from the shifted first endpoint to the even quotient.
It is a specified composite, with no choice of representatives or inverse.
Source: Stacks Project, Tag 09KP, successive quotients of the column filtration. -/
noncomputable def evenQuotientComponent (j : ℕ) (k : ℤ) :
    ((CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{u} A) ℤ) (j : ℤ)).obj
      (S j).X₁).X k ⟶ (cokernel (step K S e h_positive (2 * j))).X k :=
  lowerToOdd K S e h_positive j k ≫ (cokernel.π (step K S e h_positive (2 * j))).f k

private lemma earlierColumn_mem (j a : ℕ) (ha : a < j) (q l : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (-(a : ℤ), q) = l)
    (x : (K.X (-(a : ℤ))).X q) :
    K.ιTotal (ComplexShape.up ℤ) (-(a : ℤ)) q l h x ∈ term K S e (2 * j) l := by
  have hq : q = l + a := by dsimp at h; omega
  subst q
  apply (le_iSup (fun b : ℕ ↦
    (if 2 * b + 2 ≤ 2 * j then LinearMap.range (full K b l).hom else ⊥) ⊔
      (if 2 * b + 1 ≤ 2 * j then LinearMap.range (lower K S e b l).hom else ⊥)) a)
  apply (le_sup_left :
    (if 2 * a + 2 ≤ 2 * j then LinearMap.range (full K a l).hom else ⊥) ≤ _)
  rw [ite_eq_left (by omega)]
  exact ⟨x, rfl⟩

include h_positive in
private lemma horizontal_mem (j : ℕ) (k l : ℤ)
    (hkl : (ComplexShape.up ℤ).Rel k l) (x : (S j).X₁.X (k + j)) :
    (lower K S e j k ≫ K.D₁ (ComplexShape.up ℤ) k l) x ∈
      term K S e (2 * j) l := by
  change k + 1 = l at hkl
  simp only [lower, full, Category.assoc, HomologicalComplex₂.ι_D₁]
  cases j with
  | zero =>
    rw [K.d₁_eq (ComplexShape.up ℤ) (i₁' := 1) (by rfl) _ _ (by
      dsimp at hkl ⊢; omega)]
    have hz : K.d 0 1 = 0 := (h_positive 1 (by omega)).eq_of_tgt _ _
    simp [hz]
  | succ a =>
    rw [K.d₁_eq (ComplexShape.up ℤ) (i₁' := -(a : ℤ)) (by
      change -((a + 1 : ℕ) : ℤ) + 1 = -(a : ℤ)
      push_cast; omega) _ _ (by dsimp at hkl ⊢; omega)]
    simpa only [HomologicalComplex₂.total, ComplexShape.ε₁, TotalComplexShape.ε₁,
      one_smul, ModuleCat.comp_apply] using
      earlierColumn_mem K S e (a + 1) a (by omega) (k + (a + 1 : ℕ)) l
        (by dsimp at hkl ⊢; omega)
        ((K.d (-((a + 1 : ℕ) : ℤ)) (-(a : ℤ))).f (k + (a + 1 : ℕ))
          ((e (a + 1)).hom.f (k + (a + 1 : ℕ))
            ((S (a + 1)).f.f (k + (a + 1 : ℕ)) x)))

private lemma vertical_eq (j : ℕ) (k l : ℤ)
    (hkl : (ComplexShape.up ℤ).Rel k l) :
    lower K S e j k ≫ K.D₂ (ComplexShape.up ℤ) k l =
      (j : ℤ).negOnePow • ((S j).X₁.d (k + j) (l + j) ≫ lower K S e j l) := by
  change k + 1 = l at hkl
  simp only [lower, full, Category.assoc, HomologicalComplex₂.ι_D₂]
  rw [K.d₂_eq (ComplexShape.up ℤ) (-(j : ℤ)) (i₂' := l + j) (by
    change k + j + 1 = l + j; omega) _ (by dsimp; omega)]
  simp only [ComplexShape.ε₂, TotalComplexShape.ε₂, ComplexShape.ε_up_ℤ,
    Int.negOnePow_neg, Linear.comp_units_smul]
  rw [(e j).hom.comm_assoc, (S j).f.comm_assoc]

/-- The canonical degree maps commute with the shifted endpoint differential.
Source: Stacks Project, Tag 09KP, proof, alternating column filtration.
(blueprint: lem-pc-derived-total-filtration-even-quotient-map)

Proof. Compose with the inclusion of the odd filtration term into the total
complex. The total differential of the lower-column map is the sum of a
horizontal term and a vertical term. For j>0, the horizontal term lies in the
full column -(j-1), which is already in stage 2j; for j=0 it is zero because
column 1 is zero. The cokernel projection therefore kills this term. The
vertical term is the lower-column map composed with the endpoint differential,
by the chain-map equations for (S j).f and (e j).hom. The total sign on column
-j is (-1)^(-j)=(-1)^j, precisely the differential sign of the shift by j.
Restriction to the filtration submodules preserves these equalities since
submodule inclusions are injective. Apply the chain-map equation for the
cokernel projection to obtain the displayed equality. No exactness or freeness
is used, and this works for j=0 and for zero columns as well.
-/
theorem evenQuotientComponent_comm (j : ℕ) (k l : ℤ)
    (hkl : (ComplexShape.up ℤ).Rel k l) :
    evenQuotientComponent K S e h_positive j k ≫
      (cokernel (step K S e h_positive (2 * j))).d k l =
    ((CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{u} A) ℤ) (j : ℤ)).obj
      (S j).X₁).d k l ≫ evenQuotientComponent K S e h_positive j l  := by
  change lowerToOdd K S e h_positive j k ≫
    (cokernel.π (step K S e h_positive (2 * j))).f k ≫
      (cokernel (step K S e h_positive (2 * j))).d k l =
    ((j : ℤ).negOnePow • (S j).X₁.d (k + j) (l + j)) ≫
      lowerToOdd K S e h_positive j l ≫
        (cokernel.π (step K S e h_positive (2 * j))).f l
  let H : (S j).X₁.X (k + j) ⟶ (complex K S e h_positive (2 * j)).X l :=
    ModuleCat.ofHom ((lower K S e j k ≫ K.D₁ (ComplexShape.up ℤ) k l).hom.codRestrict
      (term K S e (2 * j) l) (horizontal_mem K S e h_positive j k l hkl))
  have hd : lowerToOdd K S e h_positive j k ≫
      (complex K S e h_positive (2 * j + 1)).d k l =
      ((j : ℤ).negOnePow • (S j).X₁.d (k + j) (l + j)) ≫ lowerToOdd K S e h_positive j l +
      H ≫ (step K S e h_positive (2 * j)).f l := by
    ext x
    apply Subtype.ext
    change ((lower K S e j k ≫ (K.total (ComplexShape.up ℤ)).d k l) x) = _
    rw [HomologicalComplex₂.total_d, Preadditive.comp_add, vertical_eq K S e j k l hkl]
    simp only [ModuleCat.hom_add, LinearMap.add_apply]
    rw [← Linear.units_smul_comp]
    exact add_comm _ _
  rw [(cokernel.π (step K S e h_positive (2 * j))).comm,
    ← Category.assoc, hd, Preadditive.add_comp, Category.assoc]
  have hz : (step K S e h_positive (2 * j)).f l ≫
      (cokernel.π (step K S e h_positive (2 * j))).f l = 0 :=
    congrArg (fun f ↦ f.f l) (cokernel.condition (step K S e h_positive (2 * j)))
  rw [Category.assoc H, hz, comp_zero, add_zero]

end CochainComplex.TotalFreeFiltration

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.TotalFreeFiltrationTerms
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift

/-!
# The canonical degree maps into the odd column quotient

Source: Stacks Project, Tag 09KP, alternating column filtration.
(blueprint: lem-pc-derived-total-filtration-odd-quotient-map)
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

/-- The full column, transported along e, enters at stage 2j+2.
Source: Stacks Project, Tag 09KP, alternating column filtration. -/
lemma full_mem_next (j : ℕ) (k : ℤ) (x : (S j).X₂.X (k + j)) :
    ((e j).hom.f (k + j) ≫ full K j k) x ∈ term K S e (2 * j + 2) k := by
  apply (le_iSup (fun a : ℕ ↦
    (if 2 * a + 2 ≤ 2 * j + 2 then LinearMap.range (full K a k).hom else ⊥) ⊔
      (if 2 * a + 1 ≤ 2 * j + 2 then LinearMap.range (lower K S e a k).hom else ⊥)) j)
  apply Submodule.mem_sup_left
  simp only [le_refl, ite_true]
  exact ⟨(e j).hom.f (k + j) x, rfl⟩

/-- The full-column map, restricted to the next filtration term.
Source: Stacks Project, Tag 09KP, alternating column filtration. -/
noncomputable def fullToNext (j : ℕ) (k : ℤ) :
    (S j).X₂.X (k + j) ⟶ (complex K S e h_positive (2 * j + 2)).X k :=
  ModuleCat.ofHom ((((e j).hom.f (k + j) ≫ full K j k)).hom.codRestrict
    (term K S e (2 * j + 2) k) (full_mem_next K S e j k))

/-- The canonical degree map from the shifted middle endpoint to the odd quotient.
It is a specified composite, with no choice of representatives or inverse.
Source: Stacks Project, Tag 09KP, successive quotients of the column filtration. -/
noncomputable def oddFullQuotientComponent (j : ℕ) (k : ℤ) :
    ((CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{u} A) ℤ) (j : ℤ)).obj
      (S j).X₂).X k ⟶ (cokernel (step K S e h_positive (2 * j + 1))).X k :=
  fullToNext K S e h_positive j k ≫ (cokernel.π (step K S e h_positive (2 * j + 1))).f k

private lemma earlierColumn_mem (j a : ℕ) (ha : a < j) (q l : ℤ)
    (h : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (-(a : ℤ), q) = l)
    (x : (K.X (-(a : ℤ))).X q) :
    K.ιTotal (ComplexShape.up ℤ) (-(a : ℤ)) q l h x ∈ term K S e (2 * j + 1) l := by
  have hq : q = l + a := by dsimp at h; omega
  subst q
  apply (le_iSup (fun b : ℕ ↦
    (if 2 * b + 2 ≤ 2 * j + 1 then LinearMap.range (full K b l).hom else ⊥) ⊔
      (if 2 * b + 1 ≤ 2 * j + 1 then LinearMap.range (lower K S e b l).hom else ⊥)) a)
  apply (le_sup_left :
    (if 2 * a + 2 ≤ 2 * j + 1 then LinearMap.range (full K a l).hom else ⊥) ≤ _)
  rw [ite_eq_left (by omega)]
  exact ⟨x, rfl⟩

include h_positive in
private lemma horizontal_mem (j : ℕ) (k l : ℤ)
    (hkl : (ComplexShape.up ℤ).Rel k l) (x : (S j).X₂.X (k + j)) :
    (((e j).hom.f (k + j) ≫ full K j k) ≫ K.D₁ (ComplexShape.up ℤ) k l) x ∈
      term K S e (2 * j + 1) l := by
  change k + 1 = l at hkl
  simp only [full, Category.assoc, HomologicalComplex₂.ι_D₁]
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
            x))

private lemma vertical_eq (j : ℕ) (k l : ℤ)
    (hkl : (ComplexShape.up ℤ).Rel k l) :
    ((e j).hom.f (k + j) ≫ full K j k) ≫ K.D₂ (ComplexShape.up ℤ) k l =
      (j : ℤ).negOnePow • ((S j).X₂.d (k + j) (l + j) ≫ 
        ((e j).hom.f (l + j) ≫ full K j l)) := by
  change k + 1 = l at hkl
  simp only [full, Category.assoc, HomologicalComplex₂.ι_D₂]
  rw [K.d₂_eq (ComplexShape.up ℤ) (-(j : ℤ)) (i₂' := l + j) (by
    change k + j + 1 = l + j; omega) _ (by dsimp; omega)]
  simp only [ComplexShape.ε₂, TotalComplexShape.ε₂, ComplexShape.ε_up_ℤ,
    Int.negOnePow_neg, Linear.comp_units_smul]
  rw [(e j).hom.comm_assoc]

/-- The full-column projection to the odd quotient is a chain map.
Source: Stacks Project, Tag 09KP, proof of lemma-resolve, alternating filtration.
(blueprint: lem-pc-derived-total-filtration-odd-quotient-map)

Proof. Restrict the full-column inclusion to stage 2j+2. Its horizontal
differential lands in an earlier full column in stage 2j+1 when j>0;
when j=0 it vanishes because the positive column is zero. The vertical
term is the differential of the middle endpoint, with sign (-1)^j.
The inclusions of submodules are injective, so this identity restricts
to the filtration stages. Composing with the cokernel projection kills
the horizontal term and gives the chain-map equation for the shift by j.
-/
theorem oddFullQuotientComponent_comm (j : ℕ) (k l : ℤ)
    (hkl : (ComplexShape.up ℤ).Rel k l) :
    oddFullQuotientComponent K S e h_positive j k ≫
      (cokernel (step K S e h_positive (2 * j + 1))).d k l =
    ((CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{u} A) ℤ) (j : ℤ)).obj
      (S j).X₂).d k l ≫ oddFullQuotientComponent K S e h_positive j l  := by
  change fullToNext K S e h_positive j k ≫
    (cokernel.π (step K S e h_positive (2 * j + 1))).f k ≫
      (cokernel (step K S e h_positive (2 * j + 1))).d k l =
    ((j : ℤ).negOnePow • (S j).X₂.d (k + j) (l + j)) ≫
      fullToNext K S e h_positive j l ≫
        (cokernel.π (step K S e h_positive (2 * j + 1))).f l
  let H : (S j).X₂.X (k + j) ⟶ (complex K S e h_positive (2 * j + 1)).X l :=
    ModuleCat.ofHom ((((e j).hom.f (k + j) ≫ full K j k) ≫
      K.D₁ (ComplexShape.up ℤ) k l).hom.codRestrict
      (term K S e (2 * j + 1) l) (horizontal_mem K S e h_positive j k l hkl))
  have hd : fullToNext K S e h_positive j k ≫
      (complex K S e h_positive (2 * j + 2)).d k l =
      ((j : ℤ).negOnePow • (S j).X₂.d (k + j) (l + j)) ≫ fullToNext K S e h_positive j l +
      H ≫ (step K S e h_positive (2 * j + 1)).f l := by
    ext x
    apply Subtype.ext
    change ((((e j).hom.f (k + j) ≫ full K j k) ≫ (K.total (ComplexShape.up ℤ)).d k l) x) = _
    rw [HomologicalComplex₂.total_d, Preadditive.comp_add, vertical_eq K S e j k l hkl]
    simp only [ModuleCat.hom_add, LinearMap.add_apply]
    rw [← Linear.units_smul_comp]
    exact add_comm _ _
  rw [(cokernel.π (step K S e h_positive (2 * j + 1))).comm,
    ← Category.assoc, hd, Preadditive.add_comp, Category.assoc]
  have hz : (step K S e h_positive (2 * j + 1)).f l ≫
      (cokernel.π (step K S e h_positive (2 * j + 1))).f l = 0 :=
    congrArg (fun f ↦ f.f l) (cokernel.condition (step K S e h_positive (2 * j + 1)))
  rw [Category.assoc H, hz, comp_zero, add_zero]

/-- The chain map from the shifted middle endpoint to the odd quotient.
Source: Stacks Project, Tag 09KP, alternating column filtration. -/
noncomputable def oddFullQuotientMap (j : ℕ) :
    ((CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{u} A) ℤ) (j : ℤ)).obj
      (S j).X₂) ⟶ cokernel (step K S e h_positive (2 * j + 1)) where
  f := oddFullQuotientComponent K S e h_positive j
  comm' := oddFullQuotientComponent_comm K S e h_positive j

/-- The lower piece is killed by the odd quotient projection.
Source: Stacks Project, Tag 09KP, definition of the alternating filtration. -/
lemma oddFullQuotientMap_zero (j : ℕ) :
    (CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{u} A) ℤ) (j : ℤ)).map
      (S j).f ≫ oddFullQuotientMap K S e h_positive j = 0 := by
  apply HomologicalComplex.Hom.ext
  funext k
  let L : (S j).X₁.X (k + j) ⟶ (complex K S e h_positive (2 * j + 1)).X k :=
    ModuleCat.ofHom ((lower K S e j k).hom.codRestrict (term K S e (2 * j + 1) k)
      (by
        intro x
        apply (le_iSup (fun a : ℕ ↦
          (if 2 * a + 2 ≤ 2 * j + 1 then LinearMap.range (full K a k).hom else ⊥) ⊔
            (if 2 * a + 1 ≤ 2 * j + 1 then
              LinearMap.range (lower K S e a k).hom else ⊥)) j)
        apply Submodule.mem_sup_right
        simp only [le_refl, ite_true]
        exact ⟨x, rfl⟩))
  have hL : (S j).f.f (k + j) ≫ fullToNext K S e h_positive j k =
      L ≫ (step K S e h_positive (2 * j + 1)).f k := by
    ext x
    rfl
  change (S j).f.f (k + j) ≫ fullToNext K S e h_positive j k ≫
    (cokernel.π (step K S e h_positive (2 * j + 1))).f k = 0
  rw [← Category.assoc, hL, Category.assoc]
  have hz := congrArg (fun f ↦ f.f k)
    (cokernel.condition (step K S e h_positive (2 * j + 1)))
  change (step K S e h_positive (2 * j + 1)).f k ≫
    (cokernel.π (step K S e h_positive (2 * j + 1))).f k = 0 at hz
  rw [hz, comp_zero]

/-- The canonical odd quotient map from the shifted third endpoint.
Its data is specified by descent through the cokernel of the shifted first
arrow; exactness determines this descent uniquely since the second arrow is epi.
Source: Stacks Project, Tag 09KP, alternating column filtration. -/
noncomputable def oddQuotientMap (h_exact : ∀ j, (S j).ShortExact) (j : ℕ) :
    ((CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{u} A) ℤ) (j : ℤ)).obj
      (S j).X₃) ⟶ cokernel (step K S e h_positive (2 * j + 1)) := by
  let F := CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{u} A) ℤ) (j : ℤ)
  have hs := (h_exact j).map_of_exact F
  have := hs.epi_g
  exact hs.exact.desc (oddFullQuotientMap K S e h_positive j)
    (oddFullQuotientMap_zero K S e h_positive j)

end CochainComplex.TotalFreeFiltration

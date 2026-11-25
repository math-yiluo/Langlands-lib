/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.TotalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.ComplexShapeSigns
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone

/-! # Explicit horizontal steps in a total-map cone

Source: Stacks Project, Homology, Tag 012X, first filtration; the columnwise
mapping-cone refinement in lem-sp-first-quadrant-vertical-cone-filtration.
-/

@[expose] public section

universe v u
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
namespace HomologicalComplex₂
variable {C : Type u} [Category.{v} C] [Abelian C]
variable [∀ L : HomologicalComplex₂ C (ComplexShape.up ℕ)
  (ComplexShape.up ℕ), L.HasTotal (ComplexShape.up ℕ)]

/-- Inclusion of a horizontal summand in the integer extension of a total complex.
It is zero if the total degree is negative. Source: Stacks 012X, first filtration.
(blueprint: lem-sp-cone-horizontal-step-stable) -/
noncomputable def coneHorizontalSummand
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (h : ℕ) (n : ℤ) :
    (K.X h).X (n.toNat - h) ⟶
      ((K.total (ComplexShape.up ℕ)).extend ComplexShape.embeddingUpNat).X n :=
  if hn : 0 ≤ n then
    K.ιTotalOrZero (ComplexShape.up ℕ) h (n.toNat - h) n.toNat ≫
      ((K.total (ComplexShape.up ℕ)).extendXIso ComplexShape.embeddingUpNat
        (Int.toNat_of_nonneg hn)).inv
  else 0

/-- Source and target summands with horizontal index `h` generate this subobject
of the cone in degree `n`. Source: Stacks 012X, columnwise cone refinement.
(blueprint: lem-sp-cone-horizontal-step-stable) -/
noncomputable def coneHorizontalImage
    {A B : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)}
    (f : A ⟶ B) (h : ℕ) (n : ℤ) :
    Subobject ((CochainComplex.mappingCone
      (HomologicalComplex.extendMap (total.map f (ComplexShape.up ℕ))
        ComplexShape.embeddingUpNat)).X n) :=
  imageSubobject (coneHorizontalSummand A h (n + 1) ≫
    HomologicalComplex.homotopyCofiber.inlX
      (HomologicalComplex.extendMap (total.map f (ComplexShape.up ℕ))
        ComplexShape.embeddingUpNat) (n + 1) n rfl) ⊔
  imageSubobject (coneHorizontalSummand B h n ≫
    (CochainComplex.mappingCone.inr
      (HomologicalComplex.extendMap (total.map f (ComplexShape.up ℕ))
        ComplexShape.embeddingUpNat)).f n)

/-- The horizontal tail is the finite sum of the source and target cone summands
whose horizontal index is at least `p`. The source total degree is `n+1`, so
indices below `n+2` suffice, also at `n=-1`. Source: Stacks 012X, first filtration.
(blueprint: lem-sp-cone-horizontal-step-stable) -/
noncomputable def coneHorizontalStep
    {A B : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)}
    (f : A ⟶ B) (p n : ℤ) :
    Subobject ((CochainComplex.mappingCone
      (HomologicalComplex.extendMap (total.map f (ComplexShape.up ℕ))
        ComplexShape.embeddingUpNat)).X n) :=
  ((Finset.range (n + 2).toNat).filter (fun h : ℕ ↦ p ≤ (h : ℤ))).sup
    (fun h ↦ coneHorizontalImage f h n)

omit [∀ L : HomologicalComplex₂ C (ComplexShape.up ℕ)
  (ComplexShape.up ℕ), L.HasTotal (ComplexShape.up ℕ)] in
/-- Multiplication by an integer preserves factorization through a subobject. -/
private theorem factors_zsmul {X Y : C} (Q : Subobject Y) (a : X ⟶ Y)
    (z : ℤ) (ha : Q.Factors a) : Q.Factors (z • a) := by
  rw [← Subobject.factorThru_arrow Q a ha, ← CategoryTheory.Preadditive.zsmul_comp]
  exact Subobject.factors_comp_arrow _

/-- The integer-extended total differential does not lower horizontal index. -/
private theorem coneHorizontalSummand_d_factors
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (h : ℕ) (n : ℤ) {Y : C} (Q : Subobject Y)
    (a : ((K.total (ComplexShape.up ℕ)).extend ComplexShape.embeddingUpNat).X (n + 1) ⟶ Y)
    (hs : ∀ i : ℕ, h ≤ i → Q.Factors (coneHorizontalSummand K i (n + 1) ≫ a)) :
    Q.Factors (coneHorizontalSummand K h n ≫
      ((K.total (ComplexShape.up ℕ)).extend ComplexShape.embeddingUpNat).d n (n + 1) ≫ a) := by
  by_cases hn : 0 ≤ n
  · by_cases hh : h ≤ n.toNat
    · have hn' : 0 ≤ n + 1 := by omega
      have hsum : (ComplexShape.up ℕ).π (ComplexShape.up ℕ) (ComplexShape.up ℕ)
          (h, n.toNat - h) = n.toNat := by change h + (n.toNat - h) = n.toNat; omega
      have hsub₁ : (n + 1).toNat - (h + 1) = n.toNat - h := by omega
      have hsub₂ : (n + 1).toNat - h = (n.toNat - h) + 1 := by omega
      have hs₁ := hs (h + 1) (by omega)
      have hs₂ := hs h le_rfl
      simp only [coneHorizontalSummand, dite_eq_left hn'] at hs₁ hs₂
      rw [hsub₁] at hs₁
      rw [hsub₂] at hs₂
      rw [coneHorizontalSummand, dite_eq_left hn,
        HomologicalComplex.extend_d_eq _ _ (Int.toNat_of_nonneg hn)
          (Int.toNat_of_nonneg hn')]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [K.ιTotalOrZero_eq _ _ _ _ hsum, total_d]
      simp only [CategoryTheory.Preadditive.add_comp,
        CategoryTheory.Preadditive.comp_add, ι_D₁_assoc, ι_D₂_assoc]
      rw [
        K.d₁_eq' _ (show (ComplexShape.up ℕ).Rel h (h + 1) by rfl),
        K.d₂_eq' _ h (show (ComplexShape.up ℕ).Rel (n.toNat - h)
          ((n.toNat - h) + 1) by rfl)]
      simp only [Category.assoc, CategoryTheory.Linear.units_smul_comp]
      apply Subobject.factors_add
      · rw [Units.smul_def]
        apply factors_zsmul
        simpa only [Category.assoc] using Subobject.factors_of_factors_right
          ((K.d h (h + 1)).f (n.toNat - h)) hs₁
      · rw [Units.smul_def]
        apply factors_zsmul
        simpa only [Category.assoc] using Subobject.factors_of_factors_right
          ((K.X h).d (n.toNat - h) ((n.toNat - h) + 1)) hs₂
    · have hz : K.ιTotalOrZero (ComplexShape.up ℕ) h (n.toNat - h) n.toNat = 0 :=
        K.ιTotalOrZero_eq_zero _ _ _ _ (by change h + (n.toNat - h) ≠ n.toNat; omega)
      simp [coneHorizontalSummand, hn, hz, Subobject.factors_zero]
  · simp [coneHorizontalSummand, hn, Subobject.factors_zero]

omit [∀ L : HomologicalComplex₂ C (ComplexShape.up ℕ)
  (ComplexShape.up ℕ), L.HasTotal (ComplexShape.up ℕ)] in
/-- A map factors through any subobject containing its image. -/
private theorem factors_image {X Y : C} (a : X ⟶ Y) (Q : Subobject Y)
    (ha : imageSubobject a ≤ Q) : Q.Factors a := by
  apply Subobject.factors_of_le a ha
  simpa using imageSubobject_factors_comp_self a (𝟙 X)

/-- Past a diagonal the summand inclusion is zero. -/
private theorem coneHorizontalSummand_eq_zero
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (h : ℕ) (n : ℤ) (hh : n.toNat < h) : coneHorizontalSummand K h n = 0 := by
  have hz : K.ιTotalOrZero (ComplexShape.up ℕ) h (n.toNat - h) n.toNat = 0 :=
    K.ιTotalOrZero_eq_zero _ _ _ _ (by change h + (n.toNat - h) ≠ n.toNat; omega)
  simp [coneHorizontalSummand, hz]

/-- A source generator with horizontal index at least p lies in the p-th tail. -/
private theorem coneHorizontalSource_factors
    {A B : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)}
    (f : A ⟶ B) (p n : ℤ) (h : ℕ) (hp : p ≤ (h : ℤ)) :
    (coneHorizontalStep f p n).Factors (coneHorizontalSummand A h (n + 1) ≫
      HomologicalComplex.homotopyCofiber.inlX
        (HomologicalComplex.extendMap (total.map f (ComplexShape.up ℕ))
          ComplexShape.embeddingUpNat) (n + 1) n rfl) := by
  by_cases hn : 0 ≤ n + 1
  · by_cases hh : h ≤ (n + 1).toNat
    · apply factors_image
      apply le_trans le_sup_left
      apply Finset.le_sup (f := fun h ↦ coneHorizontalImage f h n)
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hp⟩
    · rw [coneHorizontalSummand_eq_zero _ _ _ (by omega)]
      simp [Subobject.factors_zero]
  · simp [coneHorizontalSummand, hn, Subobject.factors_zero]

/-- A target generator with horizontal index at least p lies in the p-th tail. -/
private theorem coneHorizontalTarget_factors
    {A B : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)}
    (f : A ⟶ B) (p n : ℤ) (h : ℕ) (hp : p ≤ (h : ℤ)) :
    (coneHorizontalStep f p n).Factors (coneHorizontalSummand B h n ≫
      (CochainComplex.mappingCone.inr
        (HomologicalComplex.extendMap (total.map f (ComplexShape.up ℕ))
          ComplexShape.embeddingUpNat)).f n) := by
  by_cases hn : 0 ≤ n
  · by_cases hh : h ≤ n.toNat
    · apply factors_image
      apply le_trans le_sup_right
      apply Finset.le_sup (f := fun h ↦ coneHorizontalImage f h n)
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hp⟩
    · rw [coneHorizontalSummand_eq_zero _ _ _ (by omega)]
      simp [Subobject.factors_zero]
  · simp [coneHorizontalSummand, hn, Subobject.factors_zero]

/-- Total maps preserve the horizontal index of a summand. -/
private theorem coneHorizontalSummand_map_factors
    {A B : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)}
    (f : A ⟶ B) (h : ℕ) (n : ℤ) {Y : C} (Q : Subobject Y)
    (a : ((B.total (ComplexShape.up ℕ)).extend ComplexShape.embeddingUpNat).X n ⟶ Y)
    (hs : Q.Factors (coneHorizontalSummand B h n ≫ a)) :
    Q.Factors (coneHorizontalSummand A h n ≫
      (HomologicalComplex.extendMap (total.map f (ComplexShape.up ℕ))
        ComplexShape.embeddingUpNat).f n ≫ a) := by
  by_cases hn : 0 ≤ n
  · rw [coneHorizontalSummand, dite_eq_left hn,
      HomologicalComplex.extendMap_f _ _ (Int.toNat_of_nonneg hn)]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, ιTotalOrZero_map_assoc]
    simpa only [coneHorizontalSummand, dite_eq_left hn, Category.assoc] using
      Subobject.factors_of_factors_right ((f.f h).f (n.toNat - h)) hs
  · simp [coneHorizontalSummand, hn, Subobject.factors_zero]

/-- The cone differential preserves the explicit finite horizontal tails.
Source: Stacks Project, Homology, Tag 012X, first filtration, and the source/target
cone decomposition of the parent node, proof step 1.
(blueprint: lem-sp-cone-horizontal-step-stable)

Proof: the differential on each source summand is minus its total differential,
plus the map to the target summand in the same horizontal index. The target
summand has its total differential. Each total differential is the sum of a map
raising the horizontal index and a signed map preserving it. Every resulting
summand therefore has horizontal index at least p, so its image lies in the
next degree's tail. If an index exceeds the finite range in that degree, its
summand is zero by the first-quadrant condition. Scalar multiples and sums
of maps factoring through a subobject still factor through it. Finally the
source and target summands generate the finite supremum defining the tail:
its image under the differential is contained in the target tail, equivalently
the differential composed with its inclusion factors through that tail.
This argument also applies at n=-1 (only source degree zero survives) and
below n=-1 (the tail is zero). -/
theorem coneHorizontal_step_stable
    {A B : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)}
    (f : A ⟶ B) (p n : ℤ) :
    (coneHorizontalStep f p (n + 1)).Factors
      ((coneHorizontalStep f p n).arrow ≫
        (CochainComplex.mappingCone
          (HomologicalComplex.extendMap (total.map f (ComplexShape.up ℕ))
            ComplexShape.embeddingUpNat)).d n (n + 1)) := by
  let q := HomologicalComplex.extendMap (total.map f (ComplexShape.up ℕ))
    ComplexShape.embeddingUpNat
  let d := (CochainComplex.mappingCone q).d n (n + 1)
  let Q := coneHorizontalStep f p (n + 1)
  let P := (Subobject.pullback d).obj Q
  have hle : coneHorizontalStep f p n ≤ P := by
    apply Finset.sup_le
    intro h hh
    have hp : p ≤ (h : ℤ) := (Finset.mem_filter.mp hh).2
    apply sup_le
    · let a := coneHorizontalSummand A h (n + 1) ≫
        HomologicalComplex.homotopyCofiber.inlX q (n + 1) n rfl
      have ha : Q.Factors (a ≫ d) := by
        dsimp only [a, d]
        rw [Category.assoc]
        change Q.Factors (coneHorizontalSummand A h (n + 1) ≫
          HomologicalComplex.homotopyCofiber.inlX q (n + 1) n rfl ≫
          HomologicalComplex.homotopyCofiber.d q n (n + 1))
        rw [HomologicalComplex.homotopyCofiber.inlX_d q n (n + 1) ((n + 1) + 1)
          rfl rfl]
        simp only [CategoryTheory.Preadditive.comp_add,
          CategoryTheory.Preadditive.comp_neg]
        apply Subobject.factors_add
        · have hs := coneHorizontalSummand_d_factors A h (n + 1) Q
            (HomologicalComplex.homotopyCofiber.inlX q ((n + 1) + 1) (n + 1) rfl)
            (fun i hi ↦ coneHorizontalSource_factors f p (n + 1) i
              (hp.trans (by exact_mod_cast hi)))
          simpa only [neg_one_zsmul] using factors_zsmul Q _ (-1) hs
        · exact coneHorizontalSummand_map_factors f h (n + 1) Q
            ((CochainComplex.mappingCone.inr q).f (n + 1))
            (coneHorizontalTarget_factors f p (n + 1) h hp)
      have hf := pullback_factors d Q a ha
      exact imageSubobject_le a (P.factorThru a hf) (Subobject.factorThru_arrow _ _ _)
    · let a := coneHorizontalSummand B h n ≫ (CochainComplex.mappingCone.inr q).f n
      have ha : Q.Factors (a ≫ d) := by
        dsimp only [a, d]
        rw [Category.assoc, HomologicalComplex.Hom.comm]
        apply coneHorizontalSummand_d_factors B h n Q
        intro i hi
        exact coneHorizontalTarget_factors f p (n + 1) i
          (hp.trans (by exact_mod_cast hi))
      have hf := pullback_factors d Q a ha
      exact imageSubobject_le a (P.factorThru a hf) (Subobject.factorThru_arrow _ _ _)
  apply (pullback_factors_iff d Q _).1
  exact Subobject.factors_of_le _ hle (Subobject.factors_self _)


end HomologicalComplex₂

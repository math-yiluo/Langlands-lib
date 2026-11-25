/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ConeHorizontalProjection
public import WeilConjectures.Algebra.Homology.ConeHorizontalStepStable

/-! # Differential equation for the extended column projection

Source: Stacks Project, Homology, Tag 012X, first horizontal filtration.
(blueprint: lem-sp-horizontal-projection-tail-differential)
-/

@[expose] public section

universe v u
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
namespace HomologicalComplex₂
variable {C : Type u} [Category.{v} C] [Abelian C]
variable [∀ L : HomologicalComplex₂ C (ComplexShape.up ℕ)
  (ComplexShape.up ℕ), L.HasTotal (ComplexShape.up ℕ)]

/-- The column projection equation on a nonextended total summand. -/
@[reassoc]
private theorem totalProjection_tail_differential
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (p h m m' : ℕ) (hm' : m + 1 = m') (hp : p ≤ h) :
    K.ιTotalOrZero (ComplexShape.up ℕ) h (m - h) m ≫
      (K.total (ComplexShape.up ℕ)).d m m' ≫
      horizontalTotalProjection K p m' =
    ((-1 : ℤ) ^ p) • (K.ιTotalOrZero (ComplexShape.up ℕ) h (m - h) m ≫
      horizontalTotalProjection K p m ≫ (K.X p).d (m - p) (m' - p)) := by
  subst m'
  by_cases hh : h ≤ m
  · have hsum : (ComplexShape.up ℕ).π (ComplexShape.up ℕ) (ComplexShape.up ℕ)
        (h, m - h) = m := by change h + (m - h) = m; omega
    rw [K.ιTotalOrZero_eq _ _ _ _ hsum, total_d]
    simp only [CategoryTheory.Preadditive.comp_add, CategoryTheory.Preadditive.add_comp,
      ι_D₁_assoc, ι_D₂_assoc]
    rw [K.d₁_eq' _ (show (ComplexShape.up ℕ).Rel h (h + 1) by rfl),
      K.d₂_eq' _ h (show (ComplexShape.up ℕ).Rel (m - h) ((m - h) + 1) by rfl)]
    simp only [Category.assoc, CategoryTheory.Linear.units_smul_comp]
    rw [K.ιTotalOrZero_eq _ _ _ _ (show
      (ComplexShape.up ℕ).π (ComplexShape.up ℕ) (ComplexShape.up ℕ)
        (h + 1, m - h) = m + 1 by change h + 1 + (m - h) = m + 1; omega),
      K.ιTotalOrZero_eq _ _ _ _ (show
      (ComplexShape.up ℕ).π (ComplexShape.up ℕ) (ComplexShape.up ℕ)
        (h, (m - h) + 1) = m + 1 by change h + ((m - h) + 1) = m + 1; omega)]
    simp only [horizontalTotalProjection, ι_totalDesc, ι_totalDesc_assoc]
    have hne : h + 1 ≠ p := by omega
    simp only [dite_eq_right hne, comp_zero,
      smul_zero, zero_add]
    by_cases he : h = p
    · subst h
      have hsub : m + 1 - p = (m - p) + 1 := by omega
      simp [hsub, XXIsoOfEq, Units.smul_def]
    · simp [he]
  · have hz : K.ιTotalOrZero (ComplexShape.up ℕ) h (m - h) m = 0 :=
      K.ιTotalOrZero_eq_zero _ _ _ _ (by change h + (m - h) ≠ m; omega)
    simp [hz]

omit [∀ L : HomologicalComplex₂ C (ComplexShape.up ℕ)
  (ComplexShape.up ℕ), L.HasTotal (ComplexShape.up ℕ)] in
/-- Degree transport commutes with the canonical extension identification. -/
@[reassoc (attr := simp)]
private theorem extendIso_inv_transport
    (K : CochainComplex C ℕ) (a b : ℤ) (r : ℕ)
    (ha : (r : ℤ) = a) (hab : a = b) :
    (K.extendXIso ComplexShape.embeddingUpNat ha).inv ≫
      ((K.extend ComplexShape.embeddingUpNat).XIsoOfEq hab).hom =
    (K.extendXIso ComplexShape.embeddingUpNat (ha.trans hab)).inv := by
  subst b
  simp

/-- On a horizontal tail, column projection intertwines the total differential
with the signed vertical differential. Source: Stacks Project, Tag 012X,
first filtration and Lemma 12.25.1(1).
(blueprint: lem-sp-horizontal-projection-tail-differential)

Proof: if the total degree is negative or the horizontal index exceeds it,
the summand inclusion is zero. Otherwise write the total differential on the
summand as its horizontal term, going to index h+1, plus (-1)^h times its
vertical term, staying at index h. Since h ≥ p, projection kills the horizontal
term. If h > p, it also kills the vertical term and the original summand.
If h = p, projection identifies the summand with its column object and the
vertical term has coefficient (-1)^p. The extension and degree-equality
isomorphisms transport this equation. At total degree zero the same formula
applies; below zero its source inclusion is zero, so no boundary term occurs. -/
@[reassoc]
theorem horizontalProjection_tail_differential
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (p h : ℕ) (m i j : ℤ) (hi : m - (p : ℤ) = i)
    (hj : m + 1 - (p : ℤ) = j) (hp : p ≤ h) :
    coneHorizontalSummand K h m ≫
      ((K.total (ComplexShape.up ℕ)).extend ComplexShape.embeddingUpNat).d m (m + 1) ≫
    (horizontalExtendedProjection K p (m + 1) ≫
      (((K.X p).extend ComplexShape.embeddingUpNat).XIsoOfEq
        (show (m + 1) - (p : ℤ) = j by omega)).hom) =
    ((-1 : ℤ) ^ p) • (coneHorizontalSummand K h m ≫
    (horizontalExtendedProjection K p m ≫
      (((K.X p).extend ComplexShape.embeddingUpNat).XIsoOfEq
        (show m - (p : ℤ) = i by omega)).hom) ≫
      ((K.X p).extend ComplexShape.embeddingUpNat).d i j) := by
  by_cases hm : 0 ≤ m
  · by_cases hh : h ≤ m.toNat
    · have hp' : (p : ℤ) ≤ m := by omega
      have hm' : 0 ≤ m + 1 := by omega
      have hp'' : (p : ℤ) ≤ m + 1 := by omega
      have hn : (m + 1).toNat = m.toNat + 1 := by omega
      have hpi : ((m.toNat - p : ℕ) : ℤ) = i := by omega
      have hpj : (((m + 1).toNat - p : ℕ) : ℤ) = j := by omega
      rw [coneHorizontalSummand, dite_eq_left hm,
        HomologicalComplex.extend_d_eq _ _ (Int.toNat_of_nonneg hm)
          (Int.toNat_of_nonneg hm'),
        HomologicalComplex.extend_d_eq _ _ hpi hpj]
      simp only [horizontalExtendedProjection, dite_eq_left hp', dite_eq_left hp'',
        Category.assoc, Iso.inv_hom_id_assoc]
      erw [extendIso_inv_transport, extendIso_inv_transport_assoc]
      simp only [Iso.inv_hom_id_assoc]
      erw [totalProjection_tail_differential_assoc K p h m.toNat
        (m + 1).toNat hn.symm hp]
      simp only [CategoryTheory.Preadditive.zsmul_comp, Category.assoc]
    · have hz : K.ιTotalOrZero (ComplexShape.up ℕ) h (m.toNat - h) m.toNat = 0 :=
        K.ιTotalOrZero_eq_zero _ _ _ _
          (by change h + (m.toNat - h) ≠ m.toNat; omega)
      simp [coneHorizontalSummand, hm, hz]
  · simp [coneHorizontalSummand, hm]


end HomologicalComplex₂

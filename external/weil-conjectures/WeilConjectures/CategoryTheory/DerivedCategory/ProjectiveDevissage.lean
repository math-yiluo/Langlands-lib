/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.PrincipalIdealDevissage
public import WeilConjectures.CategoryTheory.DerivedCategory.ProjectiveSingle
public import WeilConjectures.CategoryTheory.Preadditive.FinitePowerCokernel

/-!
# Bounded complexes with projective cohomology split

Let `C` be an abelian category. A bounded object of `D(C)` all of whose cohomology objects are
projective is the direct sum of its shifted cohomology objects: the truncation triangles split,
since there are no nonzero morphisms from a projective object placed in degree `b` to an object
with vanishing `b`-th cohomology. We record this as a dévissage principle
(`DerivedCategory.prop_of_isGE_of_isLE_of_projective`): let `R` be a property of objects of `C`
satisfied by zero objects and only by projective objects; a property of objects of `D(C)`, closed
under isomorphisms, binary biproducts and shifts, satisfied by zero objects and by the objects
`X[0]` with `R X`, holds on every bounded object whose cohomology objects satisfy `R`.

This generalizes `DerivedCategory.prop_of_boundedFiniteCohomology_of_field`, where `C` is the
category of vector spaces over a field.

We also record that a property closed under isomorphisms, zero objects and binary biproducts is
closed under finite biproducts of copies of an object (`ObjectProperty.prop_biproduct_fin`).
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated

namespace CategoryTheory.ObjectProperty

variable {C : Type*} [Category C] [Preadditive C] [HasFiniteBiproducts C] [HasBinaryBiproducts C]
  (Q : ObjectProperty C) [Q.IsClosedUnderIsomorphisms]

/-- A property of objects closed under isomorphisms and binary biproducts and satisfied by zero
objects is satisfied by the finite biproducts of copies of an object satisfying it. -/
lemma prop_biproduct_fin (h₀ : ∀ X, IsZero X → Q X) (hb : ∀ X Y, Q X → Q Y → Q (X ⊞ Y))
    {X : C} (hX : Q X) (n : ℕ) : Q (⨁ fun _ : Fin n ↦ X) := by
  induction n with
  | zero => exact h₀ _ (isZero_biproduct_fin_zero _)
  | succ n ih =>
    exact Q.prop_of_iso (biproductFinSuccIso fun _ : Fin (n + 1) ↦ X).symm (hb _ _ hX ih)

end CategoryTheory.ObjectProperty

namespace DerivedCategory

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
  (R : ObjectProperty C) [R.IsClosedUnderIsomorphisms] (hR₀ : ∀ X, IsZero X → R X)
  (hRP : ∀ X, R X → Projective X)
  (Q : ObjectProperty (DerivedCategory C)) [Q.IsClosedUnderIsomorphisms]
  (h₀ : ∀ X, IsZero X → Q X) (hb : ∀ X Y, Q X → Q Y → Q (X ⊞ Y))
  (hs : ∀ X (n : ℤ), Q X → Q (X⟦n⟧)) (hQR : ∀ X, R X → Q ((singleFunctor C 0).obj X))

/-- Morphisms `M[-b] ⟶ Z` from a projective object vanish when `Hᵇ(Z) = 0`. -/
lemma eq_zero_of_singleFunctor_of_projective (b : ℤ) (M : C) [Projective M]
    (Z : DerivedCategory C) (hZ : IsZero ((homologyFunctor C b).obj Z))
    (g : (singleFunctor C b).obj M ⟶ Z) : g = 0 := by
  apply (shiftFunctor (DerivedCategory C) b).map_injective
  rw [Functor.map_zero, ← cancel_epi
    (((singleFunctors C).shiftIso b 0 b (by lia)).inv.app M), Limits.comp_zero]
  refine eq_zero_of_isZero_homology_zero M _ ?_ _
  exact hZ.of_iso (((homologyFunctor C 0).shiftIso b 0 b (by lia)).app Z)

omit [R.IsClosedUnderIsomorphisms] in
include hs hQR in
private lemma prop_single_of_projective (b : ℤ) (M : C) (hM : R M) :
    Q ((singleFunctor C b).obj M) :=
  Q.prop_of_iso (((singleFunctors C).shiftIso (-b) b 0 (by lia)).app M) (hs _ _ (hQR M hM))

include hR₀ hRP h₀ hb hs hQR in
private lemma prop_of_isGE_of_isLE_of_projective_aux (n : ℕ) :
    ∀ (a : ℤ) (M : DerivedCategory C), M.IsGE a → M.IsLE (a + n - 1) →
      (∀ q, R ((homologyFunctor C q).obj M)) → Q M := by
  induction n with
  | zero =>
    intro a M _ _ _
    have : M.IsLE (a - 1) := by simpa using ‹M.IsLE (a + ↑(0 : ℕ) - 1)›
    exact h₀ M (TStructure.t.isZero M (a - 1) a (by lia))
  | succ n ih =>
    intro a M _ _ hM
    set b : ℤ := a + n
    have hT := TStructure.t.triangleLTGE_distinguished b M
    have : ((TStructure.t.triangleLTGE b).obj M).obj₃.IsLE b := by
      have : M.IsLE b := TStructure.t.isLE_of_le M (a + ↑(n + 1) - 1) _ (by lia)
      exact inferInstanceAs (TStructure.t.IsLE ((TStructure.t.truncGE b).obj M) b)
    have : ((TStructure.t.triangleLTGE b).obj M).obj₃.IsGE b := by
      infer_instance
    obtain ⟨Y, ⟨e⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE
      ((TStructure.t.triangleLTGE b).obj M).obj₃ b
    have h₁ : IsZero ((homologyFunctor _ (b + 1)).obj ((TStructure.t.triangleLTGE b).obj M).obj₁) :=
      isZero_of_isLE _ (b - 1) _ (by lia)
    have h₀' : IsZero ((homologyFunctor _ b).obj ((TStructure.t.triangleLTGE b).obj M).obj₁) :=
      isZero_of_isLE _ (b - 1) _ (by lia)
    have := isIso_homologyMap_mor₂ _ hT b (b + 1) rfl h₀' h₁
    have hY : R Y := R.prop_of_iso
      (asIso ((homologyFunctor _ b).map ((TStructure.t.triangleLTGE b).obj M).mor₂) ≪≫
        (homologyFunctor _ b).mapIso e ≪≫ (singleFunctorCompHomologyFunctorIso _ b).app Y)
      (hM b)
    have : Projective Y := hRP Y hY
    have h₃ : Q ((TStructure.t.triangleLTGE b).obj M).obj₃ :=
      Q.prop_of_iso e.symm (prop_single_of_projective R Q hs hQR b Y hY)
    have hT₁ : Q ((TStructure.t.triangleLTGE b).obj M).obj₁ := by
      refine ih a _ ?_ ?_ fun q ↦ ?_
      · exact inferInstanceAs (TStructure.t.IsGE ((TStructure.t.truncLT b).obj M) a)
      · exact TStructure.t.isLE_truncLT_obj _ _ _ (by lia)
      · by_cases hq : q < b
        · have : IsIso ((homologyFunctor _ q).map ((TStructure.t.triangleLTGE b).obj M).mor₁) :=
            isIso_homologyMap_mor₁ _ hT (q - 1) q (by lia)
              (isZero_of_isGE _ b _ (by lia)) (isZero_of_isGE _ b _ (by lia))
          exact R.prop_of_iso (asIso ((homologyFunctor _ q).map
            ((TStructure.t.triangleLTGE b).obj M).mor₁)).symm (hM q)
        · exact hR₀ _ (isZero_of_isLE _ (b - 1) _ (by lia))
    have hmor₃ : ((TStructure.t.triangleLTGE b).obj M).mor₃ = 0 := by
      rw [← cancel_epi e.inv, Limits.comp_zero]
      have : ((TStructure.t.triangleLTGE b).obj M).obj₁.IsLE (b - 1) :=
        TStructure.t.isLE_truncLT_obj _ _ _ (by lia)
      have : (((TStructure.t.triangleLTGE b).obj M).obj₁⟦(1 : ℤ)⟧).IsLE (b - 2) :=
        TStructure.t.isLE_shift _ (b - 1) 1 (b - 2)
      refine eq_zero_of_singleFunctor_of_projective b Y _ ?_ _
      exact (isZero_of_isLE (((TStructure.t.triangleLTGE b).obj M).obj₁⟦(1 : ℤ)⟧) (b - 2) b
        (by lia))
    obtain ⟨e', -⟩ := exists_iso_binaryBiproduct_of_distTriang _ hT hmor₃
    exact Q.prop_of_iso e'.symm (hb _ _ hT₁ h₃)

include hR₀ hRP h₀ hb hs hQR in
/-- **Dévissage for bounded complexes with projective cohomology.** Let `R` be a property of
objects of `C` satisfied by zero objects and only by projective objects. A property of objects of
`D(C)`, closed under isomorphisms, binary biproducts and shifts, satisfied by zero objects and by
the objects `X[0]` with `R X`, holds on every bounded object all of whose cohomology objects
satisfy `R`: the truncation triangles of such an object split. -/
theorem prop_of_isGE_of_isLE_of_projective {M : DerivedCategory C} {a b : ℤ} (ha : M.IsGE a)
    (hb' : M.IsLE b) (hM : ∀ q, R ((homologyFunctor C q).obj M)) : Q M := by
  have : M.IsLE (a + ↑(b - a + 1).toNat - 1) := TStructure.t.isLE_of_le M b _ (by lia)
  exact prop_of_isGE_of_isLE_of_projective_aux R hR₀ hRP Q h₀ hb hs hQR (b - a + 1).toNat a M ha
    this hM

end DerivedCategory

namespace DerivedCategory

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C] (R : ObjectProperty C)

/-- An object `M` of `D(C)` is a *shifted sum* of objects satisfying `R` if it satisfies every
property of objects of `D(C)` closed under isomorphisms, binary biproducts and shifts, satisfied
by zero objects and by the objects `X[0]` with `R X`. -/
def IsShiftSum (M : DerivedCategory C) : Prop :=
  ∀ (Q : ObjectProperty (DerivedCategory C)) [Q.IsClosedUnderIsomorphisms],
    (∀ X, IsZero X → Q X) → (∀ X Y, Q X → Q Y → Q (X ⊞ Y)) → (∀ X (n : ℤ), Q X → Q (X⟦n⟧)) →
      (∀ X, R X → Q ((singleFunctor C 0).obj X)) → Q M

variable {R}

/-- A shifted sum of objects satisfying `R` satisfies every property closed under isomorphisms,
binary biproducts and shifts, satisfied by zero objects and by the objects `X[0]` with `R X`. -/
lemma IsShiftSum.prop {M : DerivedCategory C} (hM : IsShiftSum R M)
    (Q : ObjectProperty (DerivedCategory C)) [Q.IsClosedUnderIsomorphisms]
    (h₀ : ∀ X, IsZero X → Q X) (hb : ∀ X Y, Q X → Q Y → Q (X ⊞ Y))
    (hs : ∀ X (n : ℤ), Q X → Q (X⟦n⟧)) (hQR : ∀ X, R X → Q ((singleFunctor C 0).obj X)) :
    Q M :=
  hM Q h₀ hb hs hQR

/-- The shift of a shifted sum of objects satisfying `R` is one. -/
lemma IsShiftSum.shift {M : DerivedCategory C} (hM : IsShiftSum R M) (n : ℤ) :
    IsShiftSum R (M⟦n⟧) := by
  intro Q _ h₀ hb hs hQR
  let Q' : ObjectProperty (DerivedCategory C) := fun X ↦ Q (X⟦n⟧)
  have : Q'.IsClosedUnderIsomorphisms :=
    ⟨fun e h ↦ Q.prop_of_iso ((shiftFunctor _ n).mapIso e) h⟩
  refine hM Q' (fun X hX ↦ h₀ _ ((shiftFunctor _ n).map_isZero hX)) (fun X Y hX hY ↦ ?_)
    (fun X m hX ↦ Q.prop_of_iso ((shiftFunctorComm _ n m).app X) (hs _ m hX))
    (fun X hX ↦ hs _ n (hQR X hX))
  have := preservesBinaryBiproducts_of_preservesBiproducts (shiftFunctor (DerivedCategory C) n)
  exact Q.prop_of_iso ((shiftFunctor _ n).mapBiprod X Y).symm (hb _ _ hX hY)

/-- A bounded object of `D(C)` all of whose cohomology objects satisfy `R` is a shifted sum of
objects satisfying `R`, provided `R` holds for zero objects and only for projective objects. -/
lemma isShiftSum_of_isGE_of_isLE (hR₀ : ∀ X, IsZero X → R X) (hRP : ∀ X, R X → Projective X)
    [R.IsClosedUnderIsomorphisms] {M : DerivedCategory C} {a b : ℤ} (ha : M.IsGE a)
    (hb : M.IsLE b) (hM : ∀ q, R ((homologyFunctor C q).obj M)) : IsShiftSum R M :=
  fun Q _ h₀ hb' hs hQR ↦ prop_of_isGE_of_isLE_of_projective R hR₀ hRP Q h₀ hb' hs hQR ha hb hM

end DerivedCategory

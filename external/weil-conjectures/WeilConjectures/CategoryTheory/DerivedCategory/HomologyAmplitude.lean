/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE

/-!
# Upper amplitude bounds of triangulated functors between derived categories

Let `F : D(A) ⥤ D(B)` be a triangulated functor whose values on objects of `A` (placed in
degree `0`) have homology only in degrees `≤ e`. Then for an object `K` with homology in degrees
`[a, b]`, `F K` has homology only in degrees `≤ b + e`
(`DerivedCategory.isZero_homology_obj_of_isGE_of_isLE`). This is the spectral-sequence-free
form of the estimate "the `E₂^{p,q}`-terms vanish for `p > e`, so unbounded degrees can only enter
through `q`" of blueprints `rem-sf-fullcd-reduction` (3) and `rem-sf-fullcd-general-form` (a).
The proof is by induction on `b - a`, splitting `K` by the truncation triangle
`τ_{< b} K ⟶ K ⟶ τ_{≥ b} K` and using the long exact homology sequence.
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated

namespace DerivedCategory

variable {A B : Type*} [Category* A] [Abelian A] [HasDerivedCategory A] [Category* B] [Abelian B]
  [HasDerivedCategory B] (F : DerivedCategory A ⥤ DerivedCategory B) [F.CommShift ℤ]
  [F.IsTriangulated]

omit [F.IsTriangulated] in
/-- If `F` sends objects of `A` placed in degree `0` to objects with homology in degrees `≤ e`,
then it sends objects of `A` placed in degree `n` to objects with homology in degrees `≤ n + e`.
-/
lemma isZero_homology_obj_singleFunctor_obj (e : ℤ)
    (hF : ∀ (X : A) (p : ℤ), e < p →
      IsZero ((homologyFunctor B p).obj (F.obj ((singleFunctor A 0).obj X))))
    (X : A) (n r : ℤ) (hr : n + e < r) :
    IsZero ((homologyFunctor B r).obj (F.obj ((singleFunctor A n).obj X))) :=
  (hF X (r - n) (by omega)).of_iso
    ((homologyFunctor B r).mapIso (F.mapIso
        (((singleFunctors A).shiftIso (-n) n 0 (by simp)).app X).symm ≪≫
      (F.commShiftIso (-n)).app _) ≪≫
      ((homologyFunctor B 0).shiftIso (-n) r (r - n) (by omega)).app _)

/-- Upper amplitude bound: if `F` sends objects of `A` placed in degree `0` to objects with
homology in degrees `≤ e`, then it sends an object with homology in degrees `[a, b]` to an object
with homology in degrees `≤ b + e`. -/
lemma isZero_homology_obj_of_isGE_of_isLE (e : ℤ)
    (hF : ∀ (X : A) (p : ℤ), e < p →
      IsZero ((homologyFunctor B p).obj (F.obj ((singleFunctor A 0).obj X))))
    (K : DerivedCategory A) (a b : ℤ) [K.IsGE a] [K.IsLE b] (r : ℤ) (hr : b + e < r) :
    IsZero ((homologyFunctor B r).obj (F.obj K)) := by
  suffices H : ∀ (m : ℕ) (K : DerivedCategory A) (a b : ℤ), b - a ≤ m → K.IsGE a → K.IsLE b →
      ∀ r, b + e < r → IsZero ((homologyFunctor B r).obj (F.obj K)) from
    H (b - a).toNat K a b (by omega) inferInstance inferInstance r hr
  intro m
  induction m with
  | zero =>
    intro K a b hab _ _ r hr
    by_cases hlt : b < a
    · exact (homologyFunctor B r).map_isZero
        (F.map_isZero (TStructure.t.isZero K b a hlt))
    · obtain ⟨X, ⟨eX⟩⟩ : ∃ X : A, Nonempty (K ≅ (singleFunctor A b).obj X) := by
        have : K.IsGE b := TStructure.t.isGE_of_ge K b a (by omega)
        exact exists_iso_singleFunctor_obj_of_isGE_of_isLE K b
      exact (isZero_homology_obj_singleFunctor_obj F e hF X b r hr).of_iso
        ((homologyFunctor B r).mapIso (F.mapIso eX))
  | succ m ih =>
    intro K a b hab _ _ r hr
    let T := (TStructure.t.triangleLTGE b).obj K
    have hT : F.mapTriangle.obj T ∈ distTriang _ :=
      F.map_distinguished _ (TStructure.t.triangleLTGE_distinguished b K)
    have : TStructure.t.IsGE ((TStructure.t.truncLT b).obj K) a := inferInstance
    have : TStructure.t.IsLE ((TStructure.t.truncLT b).obj K) (b - 1) := inferInstance
    have : TStructure.t.IsGE ((TStructure.t.truncGE b).obj K) b := inferInstance
    have : TStructure.t.IsLE ((TStructure.t.truncGE b).obj K) b := inferInstance
    have h₁ : IsZero ((homologyFunctor B r).obj (F.obj T.obj₁)) :=
      ih T.obj₁ a (b - 1) (by omega) ‹_› ‹_› r (by omega)
    have h₃ : IsZero ((homologyFunctor B r).obj (F.obj T.obj₃)) :=
      ih T.obj₃ b b (by omega) ‹_› ‹_› r hr
    exact (HomologySequence.exact₂ _ hT r).isZero_of_both_zeros
      (h₁.eq_of_src _ _) (h₃.eq_of_tgt _ _)

end DerivedCategory

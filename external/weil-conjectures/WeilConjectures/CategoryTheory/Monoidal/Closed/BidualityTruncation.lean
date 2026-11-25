/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import WeilConjectures.SixFunctors.Etale.Derived.DoubleDual
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.ClosedTriangulated
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.TriangleShift

/-! # Finite truncation for canonical biduality

The locus where every shift of the canonical double-dual map is invertible is
triangulated. Bounded t-structure induction therefore reduces biduality to single objects.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.MonoidalClosed CategoryTheory.Pretriangulated Opposite ZeroObject

universe u v

attribute [local instance] DerivedCategory.braidedCategory'
attribute [local irreducible] DerivedCategory.monoidalClosed

namespace CategoryTheory.MonoidalClosed

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [HasDerivedCategory.{v} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]

private lemma invertible_shift_unit (n : ℤ) :
    IsInvertible ((𝟙_ (DerivedCategory C))⟦n⟧) := by
  refine ⟨(𝟙_ (DerivedCategory C))⟦-n⟧, ⟨?_⟩, ⟨?_⟩⟩
  · exact DerivedCategory.shiftTensorShiftIso C _ _ n (-n) ≪≫
      (shiftFunctor _ (n + -n)).mapIso (λ_ (𝟙_ _)) ≪≫
      (shiftFunctorZero' _ (n + -n) (by simp)).app _
  · exact DerivedCategory.shiftTensorShiftIso C _ _ (-n) n ≪≫
      (shiftFunctor _ (-n + n)).mapIso (λ_ (𝟙_ _)) ≪≫
      (shiftFunctorZero' _ (-n + n) (by simp)).app _

private lemma biduality_shift_iff (W K : DerivedCategory C) (n : ℤ) :
    IsIso (toIhomIhom W (K⟦n⟧)) ↔ IsIso (toIhomIhom W K) := by
  let e : K⟦n⟧ ≅ K ⊗ (𝟙_ _)⟦n⟧ :=
    ((((curriedTensor _).obj K).commShiftIso n).app (𝟙_ _) ≪≫
      (shiftFunctor _ n).mapIso (ρ_ K)).symm
  exact (NatTrans.isIso_app_iff_of_iso (toIhomIhomNatTrans W) e).trans
    (isIso_toIhomIhom_tensor_iff W K (invertible_shift_unit n))

private lemma doubleDual_distinguished (W : DerivedCategory C)
    (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang _) :
    ∃ w, Triangle.mk
      (((internalHom.flip.obj W).rightOp ⋙ internalHom.flip.obj W).map T.mor₁)
      (((internalHom.flip.obj W).rightOp ⋙ internalHom.flip.obj W).map T.mor₂)
      w ∈ distTriang _ := by
  obtain ⟨w, hw⟩ := DerivedCategory.exists_distinguished_ihom_pre T hT W
  obtain ⟨w', hw'⟩ := DerivedCategory.exists_distinguished_ihom_pre _ hw W
  exact ⟨w', hw'⟩

private def shiftedBidualityLocus (W : DerivedCategory C) :
    ObjectProperty (DerivedCategory C) :=
  fun K ↦ ∀ n : ℤ, IsIso (toIhomIhom W (K⟦n⟧))

private instance shiftedBidualityLocus_iso (W : DerivedCategory C) :
    (shiftedBidualityLocus W).IsClosedUnderIsomorphisms := by
  constructor
  intro K L e h n
  exact (NatTrans.isIso_app_iff_of_iso (toIhomIhomNatTrans W)
    ((shiftFunctor _ n).mapIso e)).1 (h n)

private instance shiftedBidualityLocus_shift (W : DerivedCategory C) :
    (shiftedBidualityLocus W).IsStableUnderShift ℤ := by
  constructor
  intro n
  constructor
  intro K h m
  exact (NatTrans.isIso_app_iff_of_iso (toIhomIhomNatTrans W)
    ((shiftFunctorAdd' _ n m (n + m) rfl).app K)).1 (h (n + m))

private instance shiftedBidualityLocus_zero (W : DerivedCategory C) :
    (shiftedBidualityLocus W).ContainsZero where
  exists_zero := by
    refine ⟨0, isZero_zero _, fun n ↦ ?_⟩
    have h₀ : IsZero ((0 : DerivedCategory C)⟦n⟧) :=
      (shiftFunctor _ n).map_isZero (isZero_zero _)
    have h₂ : IsZero ((ihom ((ihom ((0 : DerivedCategory C)⟦n⟧)).obj W)).obj W) :=
      isZero_ihom_obj_of_isZero (isZero_ihom_obj_of_isZero h₀ W) W
    exact ⟨⟨0, h₀.eq_of_src _ _, h₂.eq_of_src _ _⟩⟩

attribute [local irreducible] shiftedBidualityLocus

private instance shiftedBidualityLocus_ext (W : DerivedCategory C) :
    (shiftedBidualityLocus W).IsTriangulatedClosed₂ := by
  apply ObjectProperty.IsTriangulatedClosed₂.mk'
  intro T hT h₁ h₃
  unfold shiftedBidualityLocus at h₁ h₃ ⊢
  intro n
  let T' := (shiftFunctor _ n).mapTriangle.obj T
  have hT' : T' ∈ distTriang _ := (shiftFunctor _ n).map_distinguished T hT
  have : IsIso ((toIhomIhomNatTrans W).app T'.obj₁) := h₁ n
  have : IsIso ((toIhomIhomNatTrans W).app T'.obj₃) := h₃ n
  have : IsIso ((toIhomIhomNatTrans W).app (T'.obj₁⟦(1 : ℤ)⟧)) :=
    (NatTrans.isIso_app_iff_of_iso (toIhomIhomNatTrans W)
      ((shiftFunctorAdd' _ n 1 (n + 1) rfl).app T.obj₁)).1 (h₁ (n + 1))
  have : IsIso ((toIhomIhomNatTrans W).app (T'.obj₃⟦(-1 : ℤ)⟧)) :=
    (NatTrans.isIso_app_iff_of_iso (toIhomIhomNatTrans W)
      ((shiftFunctorAdd' _ n (-1) (n + -1) rfl).app T.obj₃)).1 (h₃ (n + -1))
  exact isIso_app_obj₂_of_distTriang _ (toIhomIhomNatTrans W)
    (doubleDual_distinguished W) T' hT'

private instance shiftedBidualityLocus_triangulated (W : DerivedCategory C) :
    (shiftedBidualityLocus W).IsTriangulated where

/-- Biduality on heart objects implies biduality on bounded objects.

Source: the finite truncation argument in Bhatt--Scholze, Proposition 6.8.11(3),
and the formal exactness of internal Hom (Stacks Project, Tag 08JC).
(blueprint: lem-pd-biduality-finite-truncation)

Proof: let P(K) assert invertibility of the canonical biduality map for every
integral shift of K. Naturality makes P invariant under isomorphisms, and the
shift-addition isomorphism makes it stable under shifts. It contains zero since
both internal Homs of zero are zero. Apply internal Hom twice to a distinguished
triangle. The triangulated five lemma, applied at each shift and to the adjacent
rotations, proves extension closure of P. Finite truncation induction applies
because every homology object and all its shifts have P: tensoring with the
invertible shifted unit preserves biduality by the self-adjunction argument.
Finally transport the assertion at shift zero along the zero-shift isomorphism. -/
theorem biduality_of_bounded_heart (W : DerivedCategory C)
    (Q : ObjectProperty C) [Q.IsClosedUnderIsomorphisms]
    (hQ : ∀ (M : C), Q M →
      IsIso (toIhomIhom W ((DerivedCategory.singleFunctor C 0).obj M)))
    (K : DerivedCategory C) (hb : DerivedCategory.TStructure.t.bounded K)
    (hc : ∀ n, Q ((DerivedCategory.homologyFunctor C n).obj K)) :
    IsIso (toIhomIhom W K) := by
  have h : shiftedBidualityLocus W K :=
    DerivedCategory.prop_of_bounded (shiftedBidualityLocus W) Q
      (by
        intro M hM
        unfold shiftedBidualityLocus
        intro n
        exact (biduality_shift_iff W _ n).2 (hQ M hM)) K hb hc
  unfold shiftedBidualityLocus at h
  exact (NatTrans.isIso_app_iff_of_iso (toIhomIhomNatTrans W)
    ((shiftFunctorZero _ ℤ).app K)).1 (h 0)

end CategoryTheory.MonoidalClosed

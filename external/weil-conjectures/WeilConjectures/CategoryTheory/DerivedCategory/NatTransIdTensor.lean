/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.NatTransId
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal

/-!
# Natural endomorphisms of the identity and the derived tensor product

Let `A` be a monoidal Grothendieck abelian category with functorial flat resolutions, and let
`σ : 𝟭 A ⟶ 𝟭 A` be a natural endomorphism of the identity which is compatible with the tensor
product in the sense that `σ_{M ⊗ N} = M ◁ σ_N` (for instance the multiplication by a central
scalar). Then the induced natural endomorphism `DerivedCategory.natTransId σ` of the identity of
the derived category satisfies the same compatibility with the derived tensor product
(`DerivedCategory.natTransId_app_tensor`).

The proof compares the two natural endomorphisms `(P, Z) ↦ σ_{P ⊗ Z}` and `(P, Z) ↦ P ◁ σ_Z` of
the derived tensor bifunctor, which is a left derived bifunctor, after precomposition with its
counit `μ Qh` (`NatTrans.app_tensor_eq_whiskerLeft_of_isLeftDerivedFunctor₂`); on cochain
complexes, the identity holds degreewise on each summand `X^p ⊗ Y^q` of `(X ⊗ Y)^n`
(`HomologicalComplex.natTransId_app_tensorObj`).
-/

@[expose] public section

universe u u₁

open CategoryTheory Abelian Limits MonoidalCategory

/-- Let `L : C ⥤ D` be a lax monoidal functor such that the tensor bifunctor of `D` is the left
derived bifunctor of the tensor product of `C` (with counit `μ L`). A natural endomorphism `s` of
the identity of `D` satisfies `s_{P ⊗ Z} = P ◁ s_Z` as soon as, for all `X Y : C`, there is an
endomorphism `t` of `Y` with `s_{L Y} = L t` and `s_{L (X ⊗ Y)} = L (X ◁ t)`. -/
lemma CategoryTheory.NatTrans.app_tensor_eq_whiskerLeft_of_isLeftDerivedFunctor₂
    {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
    (L : C ⥤ D) [L.LaxMonoidal] (W : MorphismProperty C) [L.IsLocalization W]
    [W.ContainsIdentities]
    [(curriedTensor D).IsLeftDerivedFunctor₂ (Functor.LaxMonoidal.μNatTrans L) W W]
    (s : 𝟭 D ⟶ 𝟭 D)
    (h : ∀ X Y : C, ∃ t : Y ⟶ Y, s.app (L.obj Y) = L.map t ∧
      s.app (L.obj (X ⊗ Y)) = L.map (X ◁ t))
    (P Z : D) :
    s.app (P ⊗ Z) = P ◁ s.app Z := by
  let γ₁ : curriedTensor D ⟶ curriedTensor D :=
    { app P :=
        { app Z := s.app (P ⊗ Z)
          naturality _ _ g := s.naturality (P ◁ g) }
      naturality _ _ f := by
        ext Z
        exact s.naturality (f ▷ Z) }
  let γ₂ : curriedTensor D ⟶ curriedTensor D :=
    { app P :=
        { app Z := P ◁ s.app Z
          naturality _ _ g := by
            dsimp
            rw [← whiskerLeft_comp, ← whiskerLeft_comp]
            exact congrArg (P ◁ ·) (s.naturality g) }
      naturality _ _ f := by
        ext Z
        exact (whisker_exchange f (s.app Z)).symm }
  have hγ : γ₁ = γ₂ := by
    refine Functor.leftDerived₂_ext (curriedTensor D) (Functor.LaxMonoidal.μNatTrans L) W W
      (curriedTensor D) γ₁ γ₂ ?_
    ext X Y
    obtain ⟨t, h₁, h₂⟩ := h X Y
    have hμ := s.naturality (Functor.LaxMonoidal.μ L X Y)
    simp only [Functor.id_obj, Functor.id_map] at hμ
    refine hμ.symm.trans ?_
    rw [h₂, ← Functor.LaxMonoidal.μ_natural_right, ← h₁]
    rfl
  exact congr_app (congr_app hγ P) Z

namespace HomologicalComplex

variable {A : Type*} [Category* A] [MonoidalCategory A] [Preadditive A] [HasZeroObject A]
  [(curriedTensor A).Additive] [∀ (X₁ : A), ((curriedTensor A).obj X₁).Additive]
  [∀ (X₁ X₂ : GradedObject ℤ A), GradedObject.HasTensor X₁ X₂]
  [∀ X₁ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).obj X₁)]
  [∀ X₂ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ A), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ A), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

/-- If a natural endomorphism `σ` of the identity of `A` satisfies `σ_{M ⊗ N} = M ◁ σ_N`, then
so does the induced levelwise endomorphism of the identity of the category of cochain
complexes. -/
lemma natTransId_app_tensorObj (σ : 𝟭 A ⟶ 𝟭 A)
    (hσ : ∀ M N : A, σ.app (M ⊗ N) = M ◁ σ.app N) (X Y : CochainComplex A ℤ) :
    (natTransId σ (ComplexShape.up ℤ)).app (X ⊗ Y) =
      X ◁ (natTransId σ (ComplexShape.up ℤ)).app Y := by
  ext n
  refine HomologicalComplex.mapBifunctor.hom_ext (fun p q hpq => ?_)
  have h := σ.naturality (ιTensorObj X Y p q n hpq)
  simp only [Functor.id_obj, Functor.id_map] at h
  rw [natTransId_app_f]
  erw [h]
  rw [hσ]
  erw [ι_mapBifunctorMap]
  simp

end HomologicalComplex

namespace DerivedCategory

variable {A : Type u₁} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A] [BraidedCategory A]
  [HasFunctorialFlatResolution A]

/-- If a natural endomorphism `σ` of the identity of `A` satisfies `σ_{M ⊗ N} = M ◁ σ_N`, then
so does the induced natural endomorphism `DerivedCategory.natTransId σ` of the identity of the
derived category, with respect to the derived tensor product. -/
lemma natTransId_app_tensor (σ : 𝟭 A ⟶ 𝟭 A)
    (hσ : ∀ M N : A, σ.app (M ⊗ N) = M ◁ σ.app N) (P Z : DerivedCategory A) :
    (natTransId σ).app (P ⊗ Z) = P ◁ (natTransId σ).app Z := by
  have := isLeftDerivedFunctor₂CurriedTensor A
  refine NatTrans.app_tensor_eq_whiskerLeft_of_isLeftDerivedFunctor₂ Qh
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) _ (fun X Y => ?_) P Z
  obtain ⟨X, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  obtain ⟨Y, rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
  refine ⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
    ((HomologicalComplex.natTransId σ (ComplexShape.up ℤ)).app Y),
    natTransId_app_Qh_obj_quotient_obj σ Y, ?_⟩
  have h := natTransId_app_Qh_obj_quotient_obj σ (X ⊗ Y)
  rw [HomologicalComplex.natTransId_app_tensorObj σ hσ] at h
  exact h

end DerivedCategory

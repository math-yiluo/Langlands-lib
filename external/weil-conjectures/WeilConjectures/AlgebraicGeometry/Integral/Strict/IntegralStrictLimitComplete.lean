/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerSystemInterface
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Principal
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

import WeilConjectures.CategoryTheory.Strict.StrictDerivedLimitMilnor
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import Mathlib.CategoryTheory.Adjunction.Evaluation
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction

/-! # Completeness of the derived strict integral quotient limit

## References

* Stacks Project, Tag 099M, and the principal orthogonality argument of Tags 091Q and 0999
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
namespace AlgebraicGeometry.ProEtale

private theorem derivedEvaluation_rightAdjoint
    {A : Type*} [Category A] [Abelian A]
    [HasDerivedCategory A] [HasDerivedCategory (ℕᵒᵖ ⥤ A)] (n : ℕᵒᵖ) :
    (((evaluation ℕᵒᵖ A).obj n).mapDerivedCategory).IsRightAdjoint := by
  classical
  have : HasFiniteBiproducts A := Abelian.hasFiniteBiproducts
  let G := evaluationLeftAdjoint A n
  have (m : ℕᵒᵖ) : PreservesFiniteLimits (G ⋙ (evaluation ℕᵒᵖ A).obj m) := by
    let e : G ⋙ (evaluation ℕᵒᵖ A).obj m ≅
        Functor.const (Discrete (n ⟶ m)) ⋙ colim :=
      NatIso.ofComponents (fun X ↦ Iso.refl _) (by
        intro X Y f
        apply Sigma.hom_ext
        intro i
        simp [G, evaluationLeftAdjoint]
        rfl)
    exact preservesFiniteLimits_of_natIso e.symm
  have : PreservesFiniteLimits G := ⟨fun J _ _ ↦
    preservesLimitsOfShape_of_evaluation G J (fun m ↦ inferInstance)⟩
  have : G.Additive := Functor.additive_of_preserves_binary_products G
  have : G.IsLeftAdjoint := (evaluationAdjunctionRight A n).isLeftAdjoint
  have : CatCommSq (G.mapHomologicalComplex (.up ℤ))
      DerivedCategory.Q DerivedCategory.Q G.mapDerivedCategory :=
    ⟨G.mapDerivedCategoryFactors.symm⟩
  let E := (evaluation ℕᵒᵖ A).obj n
  have : CatCommSq (E.mapHomologicalComplex (.up ℤ))
      DerivedCategory.Q DerivedCategory.Q E.mapDerivedCategory :=
    ⟨E.mapDerivedCategoryFactors.symm⟩
  exact ((evaluationAdjunctionRight A n).mapHomologicalComplex (.up ℤ) |>.localization
    DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ))
    G.mapDerivedCategory E.mapDerivedCategory).isRightAdjoint

private theorem integral_reduction_level_annihilated (ℓ : ℕ) (W : Scheme.{u})
    [HasDerivedCategory.{u + 1} (DiagonalAb W)]
    [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ DiagonalAb W)]
    (I : DiagonalDerivedReduction ℓ (𝟭 (DiagonalAb W)))
    (n : ℕ) (K : DerivedCategory (DiagonalAb W)) :
    ℓ ^ (n + 1) • 𝟙
      (((evaluation ℕᵒᵖ (DiagonalAb W)).obj (Opposite.op n)).mapDerivedCategory.obj
        (I.T.obj K)) = 0 := by
  let V := ((evaluation ℕᵒᵖ (DiagonalAb W)).obj (Opposite.op n)).mapDerivedCategory
  let F := I.ordinary.E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  have : V.IsRightAdjoint := derivedEvaluation_rightAdjoint (Opposite.op n)
  have := I.universal
  have := I.pointwise
  have : Functor.HasPointwiseRightKanExtension DerivedCategory.Q F :=
    Functor.hasPointwiseRightKanExtension_of_hasPointwiseLeftDerivedFunctor F
      DerivedCategory.Q (HomologicalComplex.quasiIso (DiagonalAb W) (.up ℤ))
  have : I.T.IsRightKanExtension I.ε :=
    Functor.IsLeftDerivedFunctor.isRightKanExtension I.T I.ε
      (HomologicalComplex.quasiIso (DiagonalAb W) (.up ℤ))
  let β : DerivedCategory.Q ⋙ (I.T ⋙ V) ⟶ F ⋙ V :=
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight I.ε V
  have : (I.T ⋙ V).IsRightKanExtension β := inferInstance
  have hz (P : CochainComplex (DiagonalAb W) ℤ) :
      ℓ ^ (n + 1) • 𝟙 ((F ⋙ V).obj P) = 0 := by
    let q := ((evaluation ℕᵒᵖ (DiagonalAb W)).obj (Opposite.op n)).mapDerivedCategoryFactors
    apply (cancel_mono (q.hom.app
      ((I.ordinary.E.mapHomologicalComplex (.up ℤ)).obj P))).1
    rw [zero_comp, Preadditive.nsmul_comp, Category.id_comp,
      ← Category.comp_id (q.hom.app
        ((I.ordinary.E.mapHomologicalComplex (.up ℤ)).obj P)),
      ← Preadditive.comp_nsmul]
    have hq : ℓ ^ (n + 1) • 𝟙
        ((((evaluation ℕᵒᵖ (DiagonalAb W)).obj (Opposite.op n)).mapHomologicalComplex
          (.up ℤ)).obj ((I.ordinary.E.mapHomologicalComplex (.up ℤ)).obj P)) = 0 := by
      apply HomologicalComplex.Hom.ext
      funext i
      change ℓ ^ (n + 1) • 𝟙
        ((I.ordinary.E ⋙ (evaluation ℕᵒᵖ (DiagonalAb W)).obj
          (Opposite.op n)).obj (P.X i)) = 0
      have : Epi ((I.ordinary.π n).app (P.X i)) :=
        Cofork.IsColimit.epi (I.ordinary.quotient n (P.X i))
      apply (cancel_epi ((I.ordinary.π n).app (P.X i))).1
      rw [comp_zero, Preadditive.comp_nsmul, Category.comp_id]
      simpa only [Preadditive.nsmul_comp, Category.id_comp] using
        I.ordinary.zero n (P.X i)
    have hh := congrArg (fun f ↦ DerivedCategory.Q.{u + 1}.map f) hq
    simpa only [Functor.comp_obj, Functor.map_nsmul, CategoryTheory.Functor.map_id,
      Functor.map_zero, comp_zero] using congrArg
        (fun f ↦ q.hom.app ((I.ordinary.E.mapHomologicalComplex (.up ℤ)).obj P) ≫ f) hh
  have hnat : ℓ ^ (n + 1) • 𝟙 (I.T ⋙ V) = 0 := by
    apply Functor.hom_ext_of_isRightKanExtension (I.T ⋙ V) β
    ext P
    change (ℓ ^ (n + 1) • 𝟙 _) ≫ β.app P = 0 ≫ β.app P
    rw [zero_comp, Preadditive.nsmul_comp, Category.id_comp,
      ← Category.comp_id (β.app P), ← Preadditive.comp_nsmul, hz, comp_zero]
  exact NatTrans.congr_app hnat K

/-- The strict derived quotient limit is derived complete after identifying coefficients.
This is only the assertion about its values; it specifies no augmentation or reflector. -/
theorem integral_strict_limit_complete (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    [HasDerivedCategory.{u + 1} (DiagonalAb W)]
    [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ DiagonalAb W)]
    (I : DiagonalDerivedReduction ℓ (𝟭 (DiagonalAb W)))
    (RZ : DerivedCategory (ℕᵒᵖ ⥤ DiagonalAb W) ⥤ DerivedCategory (DiagonalAb W))
    (ηZ : (lim : (ℕᵒᵖ ⥤ DiagonalAb W) ⥤ DiagonalAb W).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RZ)
    (hRZ : RZ.IsRightDerivedFunctor ηZ
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ DiagonalAb W) (.up ℤ)))
    (e : DiagonalAb W ≌
      Sheaf (Scheme.ProEt.topology W) (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)))
    [e.functor.Additive] [e.inverse.Additive] :
    ∀ K : DerivedCategory (DiagonalAb W),
      DerivedCategory.derivedComplete (Scheme.ProEt.topology W)
        (Ideal.span {(ℓ : ULift.{u + 1} ℤ)})
        (((I.T ⋙ RZ) ⋙ e.mapDerivedCategory.functor).obj K) := by
  let A := DiagonalAb W
  let ed := e.functor.mapDerivedCategory
  have : ed.Additive := Functor.additive_of_preserves_binary_products ed
  let : IsGrothendieckAbelian.{u + 1} A := inferInstance
  let : HasCountableProducts (DerivedCategory A) :=
    ⟨fun J _ ↦ DerivedCategory.hasLimitsOfShape_discrete A J⟩
  obtain ⟨E, ε, p, δ, hT⟩ := strictDerivedLimit_milnor RZ ηZ hRZ
  intro K
  let Z := I.T.obj K
  let X := DerivedCategory.Q.objPreimage Z
  let x := DerivedCategory.Q.objObjPreimageIso Z
  have hn (n : ℕ) : ℓ ^ (n + 1) • 𝟙 ((E.obj Z).obj (Opposite.op n)) = 0 := by
    let v := (evaluation ℕᵒᵖ A).obj (Opposite.op n)
    let z : (E.obj Z).obj (Opposite.op n) ≅ v.mapDerivedCategory.obj Z :=
      ((Functor.mapIso E x.symm).app (Opposite.op n)) ≪≫
        ((ε.app X).app (Opposite.op n)) ≪≫
        (v.mapDerivedCategoryFactors.app X).symm ≪≫ v.mapDerivedCategory.mapIso x
    apply (cancel_mono z.hom).1
    rw [zero_comp, Preadditive.nsmul_comp, Category.id_comp,
      ← Category.comp_id z.hom, ← Preadditive.comp_nsmul]
    rw [integral_reduction_level_annihilated ℓ W I n K, comp_zero]
  let P : Fan fun n : ℕ ↦ ed.obj ((E.obj Z).obj (Opposite.op n)) :=
    Fan.mk (ed.obj (∏ᶜ (fun n : ℕ ↦ (E.obj Z).obj (Opposite.op n))))
      (fun n ↦ ed.map (Pi.π _ n))
  have hP : IsLimit P :=
    (Fan.isLimitMapConeEquiv ed _ (limit.cone _))
      (isLimitOfPreserves ed (limit.isLimit _))
  let T := ed.mapTriangle.obj (Triangle.mk (p Z)
    (towerTransitionEndomorphism
      (fun n : ℕ ↦ (E.obj Z).map (homOfLE (Nat.le_succ n)).op)) (δ Z))
  have ht : T ∈ distTriang _ := ed.map_distinguished _ (hT Z)
  have hnil (n : ℕ) :
      ℓ ^ (n + 1) • 𝟙 (ed.obj ((E.obj Z).obj (Opposite.op n))) = 0 := by
    simpa only [Functor.map_nsmul, CategoryTheory.Functor.map_id, Functor.map_zero] using
      congrArg (fun f ↦ ed.map f) (hn n)
  have ho : (DerivedCategory.smulInvertible (Scheme.ProEt.topology W)
      (ℓ : ULift.{u + 1} ℤ)).rightOrthogonal (ed.obj (RZ.obj Z)) := by
    intro L f hL
    have h₀ : f ≫ T.mor₁ = 0 := Fan.IsLimit.hom_ext hP _ _ fun n ↦ by
      rw [zero_comp]
      exact hL.hom_eq_zero (n := n + 1)
        (by
          rw [← Nat.cast_pow]
          exact (@Nat.cast_smul_eq_nsmul (ULift.{u + 1} ℤ) _ _ _
            (CategoryTheory.Linear.homModule
              (ed.obj ((E.obj Z).obj (Opposite.op n)))
              (ed.obj ((E.obj Z).obj (Opposite.op n)))) _ _).trans (hnil n)) _
    obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₁ T ht (f⟦(1 : ℤ)⟧')
      (by rw [← Functor.map_comp, h₀, Functor.map_zero])
    have : g = 0 := Fan.IsLimit.hom_ext hP _ _ fun n ↦ by
      rw [zero_comp]
      exact (ObjectProperty.le_shift _ 1 L hL).hom_eq_zero (n := n + 1)
        (by
          rw [← Nat.cast_pow]
          exact (@Nat.cast_smul_eq_nsmul (ULift.{u + 1} ℤ) _ _ _
            (CategoryTheory.Linear.homModule
              (ed.obj ((E.obj Z).obj (Opposite.op n)))
              (ed.obj ((E.obj Z).obj (Opposite.op n)))) _ _).trans (hnil n)) _
    rw [this, zero_comp] at hg
    exact (shiftFunctor _ (1 : ℤ)).map_eq_zero_iff.mp hg
  have hr : (ℓ : ULift.{u + 1} ℤ) ∈ nonZeroDivisors (ULift.{u + 1} ℤ) := by
    rw [mem_nonZeroDivisors_iff]
    have hleft : ∀ y : ULift.{u + 1} ℤ, (ℓ : ULift.{u + 1} ℤ) * y = 0 → y = 0 := by
      intro y hy
      apply ULift.ext
      change y.down = 0
      have h : (ℓ : ℤ) * y.down = 0 := congrArg ULift.down hy
      exact (mul_eq_zero.mp h).resolve_left
        (by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero)
    exact ⟨hleft, fun y hy ↦ hleft y ((mul_comm _ _).trans hy)⟩
  exact DerivedCategory.derivedComplete_of_rightOrthogonal hr rfl ho

end AlgebraicGeometry.ProEtale

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerSystemInterface
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Completion
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Whiskering

import WeilConjectures.AlgebraicGeometry.Integral.Strict.IntegralStrictLimitComplete
import WeilConjectures.AlgebraicGeometry.Integral.Strict.IntegralStrictLimitAugmentationTriangle

/-! # Comparison of the strict integral completion with the source completion

## References

* Stacks Project, Tag 099M
* Stacks 06YY, uniqueness of total derived functors
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
namespace AlgebraicGeometry.ProEtale

/-- The additive equivalence identifying abelian sheaves with modules over the lifted integers. -/
def integralCompletionCoefficientEquivalence (W : Scheme.{u}) :
    DiagonalAb W ≌ Sheaf (Scheme.ProEt.topology W) (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) := by
  let F := ModuleCat.restrictScalars
      (ULift.ringEquiv.symm.toRingHom : ℤ →+* ULift.{u + 1} ℤ) ⋙
    forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}
  have : F.IsEquivalence := inferInstance
  have : (sheafCompose (Scheme.ProEt.topology W) F).IsEquivalence :=
    isEquivalence_sheafCompose_of_isEquivalence _ F
  exact (sheafCompose (Scheme.ProEt.topology W) F).asEquivalence.symm

/-- The coefficient identification is additive. -/
instance integralCompletionCoefficientEquivalence_additive (W : Scheme.{u}) :
    (integralCompletionCoefficientEquivalence W).functor.Additive := by
  exact Functor.additive_of_preserves_binary_products _

/-- The inverse coefficient identification is additive. -/
instance integralCompletionCoefficientEquivalence_inverse_additive (W : Scheme.{u}) :
    (integralCompletionCoefficientEquivalence W).inverse.Additive := by
  exact Functor.additive_of_preserves_binary_products _

/-- A prime remains a nonzerodivisor in the lifted integers. -/
theorem integralCompletionPrimeRegular (ℓ : ℕ) [Fact ℓ.Prime] :
    (ℓ : ULift.{u + 1} ℤ) ∈ nonZeroDivisors (ULift.{u + 1} ℤ) := by
  rw [mem_nonZeroDivisors_iff]
  have hleft : ∀ x : ULift.{u + 1} ℤ, (ℓ : ULift.{u + 1} ℤ) * x = 0 → x = 0 := by
    intro x hx
    apply ULift.ext
    change x.down = 0
    have h : (ℓ : ℤ) * x.down = 0 := congrArg ULift.down hx
    exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero)
  exact ⟨hleft, fun x hx ↦ hleft x ((mul_comm _ _).trans hx)⟩

/-- The standard completion endofunctor on integer-module sheaves, with no change of scalars. -/
def integralModuleCompletion (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u}) :=
  DerivedCategory.derivedCompletion (Scheme.ProEt.topology W)
    (Ideal.span {(ℓ : ULift.{u + 1} ℤ)})
    ⟨(ℓ : ULift.{u + 1} ℤ), integralCompletionPrimeRegular ℓ, rfl⟩ ⋙
  (DerivedCategory.derivedComplete (Scheme.ProEt.topology W)
    (Ideal.span {(ℓ : ULift.{u + 1} ℤ)})).ι

universe a b va vb

private theorem comparison_of_complete_and_triangle
    {A : Type a} [Category.{va} A] {C : Type b} [Category.{vb} C]
    [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (S P : ObjectProperty C) [S.IsStableUnderShift ℤ]
    (L : C ⥤ P.FullSubcategory) (adj : L ⊣ P.ι)
    (hP : ∀ Y, P Y → S.rightOrthogonal Y)
    (E F : A ⥤ C) (η : E ⟶ F) (hF : ∀ K, P (F.obj K))
    (hη : ∀ K, ∃ (X : C) (g : F.obj K ⟶ X) (h : X ⟶ (E.obj K)⟦(1 : ℤ)⟧),
      Pretriangulated.Triangle.mk (η.app K) g h ∈ distTriang C ∧ S X) :
    Nonempty (F ≅ E ⋙ (L ⋙ P.ι)) := by
  let α (K : A) : L.obj (E.obj K) ⟶ (⟨F.obj K, hF K⟩ : P.FullSubcategory) :=
    (adj.homEquiv (E.obj K) ⟨F.obj K, hF K⟩).symm (η.app K)
  have hα (K : A) : adj.unit.app (E.obj K) ≫ (α K).hom = η.app K :=
    (adj.homEquiv (E.obj K) ⟨F.obj K, hF K⟩).apply_symm_apply (η.app K)
  have hi (K : A) : IsIso (α K) := by
    obtain ⟨X, g, h, hT, hX⟩ := hη K
    apply isIso_of_coyoneda_map_bijective
    intro Y
    have hb := ObjectProperty.bijective_comp_of_distinguished hT hX (hP _ Y.property)
    constructor
    · intro f g hfg
      apply ObjectProperty.hom_ext
      apply hb.1
      have he := congrArg (fun z ↦ adj.unit.app (E.obj K) ≫ z.hom) hfg
      simpa only [ObjectProperty.FullSubcategory.comp_hom, ← Category.assoc, hα] using he
    · intro f
      obtain ⟨g, hg⟩ := hb.2 ((adj.homEquiv (E.obj K) Y) f)
      refine ⟨ObjectProperty.homMk g, ?_⟩
      apply (adj.homEquiv (E.obj K) Y).injective
      change adj.unit.app (E.obj K) ≫ ((α K).hom ≫ g) = _
      rw [← Category.assoc, hα]
      exact hg
  have hinj (K K' : A) : Function.Injective
      (fun f : (L.obj (E.obj K)).obj ⟶ F.obj K' ↦ adj.unit.app (E.obj K) ≫ f) := by
    intro f g hfg
    exact congrArg InducedCategory.Hom.hom
      ((adj.homEquiv (E.obj K) ⟨F.obj K', hF K'⟩).injective hfg)
  have hi' (K : A) : IsIso (α K).hom := by
    let := hi K
    infer_instance
  let c : E ⋙ (L ⋙ P.ι) ≅ F := NatIso.ofComponents
    (fun K ↦ by letI := hi' K; exact asIso (α K).hom) (by
      intro K K' f
      apply hinj K K'
      change adj.unit.app (E.obj K) ≫ ((L.map (E.map f)).hom ≫ (α K').hom) =
        adj.unit.app (E.obj K) ≫ ((α K).hom ≫ F.map f)
      have hu : E.map f ≫ adj.unit.app (E.obj K') =
          adj.unit.app (E.obj K) ≫ (L.map (E.map f)).hom :=
        adj.unit.naturality (E.map f)
      rw [← Category.assoc, ← hu, Category.assoc, hα, ← Category.assoc, hα]
      exact η.naturality f)
  exact ⟨c.symm⟩

/-- The strict integral quotient completion agrees naturally with the standard integer-module
completion after the additive coefficient identification. -/
theorem integral_strict_completion_comparison (ℓ : ℕ) [Fact ℓ.Prime] (W : Scheme.{u})
    [HasDerivedCategory.{u + 1} (DiagonalAb W)]
    [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ DiagonalAb W)]
    (I : DiagonalDerivedReduction ℓ (𝟭 (DiagonalAb W)))
    (RZ : DerivedCategory (ℕᵒᵖ ⥤ DiagonalAb W) ⥤ DerivedCategory (DiagonalAb W))
    (ηZ : (lim : (ℕᵒᵖ ⥤ DiagonalAb W) ⥤ DiagonalAb W).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ RZ)
    (hRZ : RZ.IsRightDerivedFunctor ηZ
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ DiagonalAb W) (.up ℤ))) :
    Nonempty ((I.T ⋙ RZ) ⋙ (integralCompletionCoefficientEquivalence W).mapDerivedCategory.functor ≅
      (integralCompletionCoefficientEquivalence W).mapDerivedCategory.functor ⋙
        integralModuleCompletion ℓ W) := by
  let e := integralCompletionCoefficientEquivalence W
  let J := Scheme.ProEt.topology W
  let r : ULift.{u + 1} ℤ := ℓ
  let P := DerivedCategory.derivedComplete J (Ideal.span {r})
  let S := DerivedCategory.smulInvertible J r
  let L := DerivedCategory.derivedCompletion J (Ideal.span {r})
    ⟨r, integralCompletionPrimeRegular ℓ, rfl⟩
  let adj := DerivedCategory.derivedCompletionAdjunction J (Ideal.span {r})
    ⟨r, integralCompletionPrimeRegular ℓ, rfl⟩
  obtain ⟨η, hη⟩ := integral_strict_limit_augmentation_triangle ℓ W I RZ ηZ hRZ e
  exact comparison_of_complete_and_triangle S P L adj
    (fun _ hY ↦ DerivedCategory.rightOrthogonal_of_derivedComplete
      (Ideal.subset_span (Set.mem_singleton r)) hY)
    e.mapDerivedCategory.functor ((I.T ⋙ RZ) ⋙ e.mapDerivedCategory.functor) η
    (integral_strict_limit_complete ℓ W I RZ ηZ hRZ e) hη

end AlgebraicGeometry.ProEtale

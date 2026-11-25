/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.TensorQuotPow

/-!
# The reduction maps `K ⟶ K ⊗ᴸ R/ϖⁿ` complete multiplication by `ϖⁿ` to a triangle

Let `(C, J)` be an essentially small site, `R` a commutative ring and `ϖ ∈ R` a nonzerodivisor
generating the ideal `I`. For an object `K` of `D(J, R)`, the reduction map
`K ⟶ K ⊗ᴸ R/Iⁿ`, the `n`-th leg of `DerivedCategory.derivedCompletionCone J I K`, is the second
map of a distinguished triangle `K ──ϖⁿ──▶ K ⟶ K ⊗ᴸ R/Iⁿ ⟶ K⟦1⟧`
(`DerivedCategory.exists_distTriang_derivedCompletionCone`): the triangle
`R ⟶ R ⟶ R/Iⁿ ⟶ R⟦1⟧` tensored with `K`.

The statement does not mention the monoidal structure of `D(J, R)`, which is the one of
`DerivedCategory.sheafTensorStructure J R`, as explained in the implementation notes of
`WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs`.
-/

@[expose] public section

universe u

open CategoryTheory Category Limits MonoidalCategory Opposite Pretriangulated

namespace DerivedCategory

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) {R : Type (u + 1)} [CommRing R]

attribute [-instance] commShift₂CurriedTensor commShiftTensorLeft commShiftTensorRight
  isTriangulated_tensorLeft isTriangulated_tensorRight monoidalPreadditive monoidalLinear

noncomputable local instance (priority := high) reductionTriangleInst1 :
    MonoidalCategory (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :=
  (sheafTensorStructure J R).monoidalCategory

noncomputable local instance (priority := high) reductionTriangleInst2 :
    MonoidalPreadditive (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :=
  (sheafTensorStructure J R).monoidalPreadditive

noncomputable local instance (priority := high) reductionTriangleInst3 :
    MonoidalLinear R (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :=
  (sheafTensorStructure J R).monoidalLinear

noncomputable local instance (priority := high) reductionTriangleInst4 :
    (curriedTensor (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)))).CommShift₂Int :=
  (sheafTensorStructure J R).commShift₂

noncomputable local instance (priority := high) reductionTriangleInst5
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    ((curriedTensor (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)))).obj K).IsTriangulated :=
  (sheafTensorStructure J R).isTriangulated_tensorLeft K

local instance reductionTriangleInstε : IsIso (sheafTensorStructure J R).ε :=
  (sheafTensorStructure J R).isIso_ε

variable {J} {I : Ideal R} {ϖ : R} (hϖ : ϖ ∈ nonZeroDivisors R) (hI : I = Ideal.span {ϖ})

include hϖ hI in
/-- The `n`-th reduction map `K ⟶ K ⊗ᴸ R/Iⁿ` of `DerivedCategory.derivedCompletionCone` is the
second map of a distinguished triangle `K ──ϖⁿ──▶ K ⟶ K ⊗ᴸ R/Iⁿ ⟶ K⟦1⟧`. -/
lemma exists_distTriang_derivedCompletionCone
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) (n : ℕ) :
    ∃ h : (derivedCompletionDiagram J I K).obj (op n) ⟶ K⟦(1 : ℤ)⟧,
      Triangle.mk (ϖ ^ n • 𝟙 K) ((derivedCompletionCone J I K).π.app (op n)) h ∈
        distTriang _ := by
  let T := tensorQuotPowTriangle hϖ hI K n
  let e := unitIso K
  have hmor : T.mor₁ = ϖ ^ n • 𝟙 T.obj₁ := by
    change K ◁ (quotPowTriangle J hϖ hI n).mor₁ = _
    rw [quotPowTriangle_mor₁, MonoidalLinear.whiskerLeft_smul, MonoidalCategory.whiskerLeft_id]
    rfl
  refine ⟨T.mor₃ ≫ e.inv⟦(1 : ℤ)⟧', isomorphic_distinguished _
    (tensorQuotPowTriangle_distinguished hϖ hI K n) _
    (Triangle.isoMk _ _ e e (Iso.refl _) ?_ ?_ ?_)⟩
  · change (ϖ ^ n • 𝟙 K) ≫ e.hom = e.hom ≫ T.mor₁
    rw [hmor, Linear.smul_comp, Linear.comp_smul, id_comp]
    erw [comp_id]
  · change (derivedCompletionCone J I K).π.app (op n) ≫ 𝟙 _ = e.hom ≫ T.mor₂
    rw [comp_id, derivedCompletionCone_π_app hϖ hI]
  · change (T.mor₃ ≫ e.inv⟦(1 : ℤ)⟧') ≫ e.hom⟦(1 : ℤ)⟧' = 𝟙 _ ≫ T.mor₃
    rw [assoc, ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id, comp_id,
      id_comp]

end DerivedCategory

/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.FromJoel.Algebra.Homology.DerivedCategory.Monoidal

/-!
# The unit comparison of `Qh : K(C) ⥤ D(C)`

The unit comparison `ε : 𝟙_ ⟶ Qh (𝟙_)` of the lax monoidal functor `Qh` is an isomorphism.

Stating this once for a general category `C` lets a concrete category (such as étale sheaves on a
scheme) use it as a plain application. Deriving it at a concrete category through
`inferInstanceAs` makes the kernel compare the two paths to the lax monoidal structure of `Qh`
there, which takes about a minute.
-/

@[expose] public section

open CategoryTheory MonoidalCategory

universe w v u

namespace DerivedCategory

variable (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  [MonoidalCategory C] [MonoidalPreadditive C]
  [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [Qh.HasDerivedMonoidalCategory (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]

/-- The unit comparison `𝟙_ ⟶ Qh (𝟙_)` of `Qh : K(C) ⥤ D(C)` is an isomorphism. -/
theorem isIso_ε_Qh : IsIso (Functor.LaxMonoidal.ε (Qh (C := C))) :=
  inferInstanceAs (IsIso (Functor.LaxMonoidal.ε (toDerivedMonoidal Qh
    (HomotopyCategory.quasiIso C (.up ℤ)))))

end DerivedCategory

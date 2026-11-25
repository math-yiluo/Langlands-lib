/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.ClosedTriangulated
public import WeilConjectures.CategoryTheory.DerivedCategory.BifunctorHom

/-!
# The internal hom of the derived category on K-injective targets, as a functor

Let `C` be a monoidal closed Grothendieck abelian category whose derived category is monoidal
closed (`DerivedCategory.monoidalClosed`), and `J` a K-injective complex. The hom complexes
`N ↦ Hom(N, J)` of the internal hom bifunctor of `C`
(`DerivedCategory.bifunctorHomQFunctor MonoidalClosed.internalHom J`) compute the internal hom
`N ↦ [N, J]` of `D(C)`, naturally in the complex `N`
(`DerivedCategory.bifunctorHomQFunctorIsoIhom`). This repackages
`DerivedCategory.qhInternalHomToIhom` as a natural isomorphism of functors of the source.
-/

@[expose] public section

open CategoryTheory Category Limits MonoidalCategory Opposite
open MonoidalClosed hiding assoc id_comp comp_id

universe w v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalClosed C] [MonoidalPreadditive C] [HasCountableProducts C]

/-- The internal hom of a monoidal closed preadditive category is additive in its source. -/
instance internalHom_additive : (MonoidalClosed.internalHom (C := C)).Additive where
  map_add {_ _ f g} := NatTrans.ext (funext fun X ↦ pre_add_app f.unop g.unop X)

instance (X : Cᵒᵖ) : ((MonoidalClosed.internalHom (C := C)).obj X).Additive :=
  inferInstanceAs (ihom X.unop).Additive

/-- The hom complex of the internal hom bifunctor is the internal hom complex. -/
lemma bifunctorHomObj_internalHom (N J : CochainComplex C ℤ) :
    bifunctorHomObj MonoidalClosed.internalHom N J = internalHomObj N J :=
  rfl


variable [HasZeroObject C] [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]

/-- Precomposition on hom complexes of the internal hom bifunctor is precomposition on internal
hom complexes. -/
lemma bifunctorHomMapLeft_internalHom {N N' : CochainComplex C ℤ} (g : N' ⟶ N)
    (J : CochainComplex C ℤ) :
    bifunctorHomMapLeft (H := MonoidalClosed.internalHom) (Y := J) g = internalHomPre g J := by
  ext n p q h
  erw [internalHomPre_f_π, bifunctorHomMapLeft_f_π]
  rfl

end CochainComplex

namespace DerivedCategory

section

variable {A : Type*} [Category* A] [Abelian A] [HasCountableProducts A] [HasDerivedCategory A]
  (H : Aᵒᵖ ⥤ A ⥤ A) [∀ X, (H.obj X).Additive] [H.Additive] (J : CochainComplex A ℤ)

/-- The hom complexes `N ↦ Hom_H(N, J)` into a fixed complex, as a functor to the derived
category. -/
@[simps]
noncomputable def bifunctorHomQFunctor : (CochainComplex A ℤ)ᵒᵖ ⥤ DerivedCategory A where
  obj N := Q.obj (CochainComplex.bifunctorHomObj H N.unop J)
  map g := Q.map (CochainComplex.bifunctorHomMapLeft (H := H) (Y := J) g.unop)
  map_id N := by
    rw [unop_id, CochainComplex.bifunctorHomMapLeft_id, Q.map_id]
  map_comp f g := by
    rw [unop_comp, CochainComplex.bifunctorHomMapLeft_comp, Q.map_comp]

end

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  [HasDerivedCategory.{w} C]
  [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C]
  [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [(HomotopyCategory.quasiIso C
    (ComplexShape.up ℤ)).localizerMorphismKFlat.IsLeftDerivabilityStructure]

/-- The comparison `Q Hom(N, J) ⟶ [N, J]`, through `Q ≅ Qh ∘ quotient`, is natural in `N`. -/
lemma qhInternalHomToIhom_naturality' {N N' : CochainComplex C ℤ} (g : N' ⟶ N)
    (J : CochainComplex C ℤ) :
    Q.map (CochainComplex.bifunctorHomMapLeft (H := MonoidalClosed.internalHom) (Y := J) g) ≫
        ((quotientCompQhIso C).inv.app (CochainComplex.internalHomObj N' J) ≫
          qhInternalHomToIhom N' J) =
      ((quotientCompQhIso C).inv.app (CochainComplex.internalHomObj N J) ≫
          qhInternalHomToIhom N J) ≫
        (pre (Qh.map ((HomotopyCategory.quotient C _).map g))).app _ := by
  erw [CochainComplex.bifunctorHomMapLeft_internalHom, reassoc_of% quotientCompQhIso_inv_naturality]
  erw [qhInternalHomToIhom_naturality]
  exact (assoc _ _ _).symm

/-- **The hom complex into a K-injective complex computes the internal hom of `D(C)`**, as a
natural isomorphism `Hom(N, J) ≅ [N, J]` of functors of the complex `N`. -/
noncomputable def bifunctorHomQFunctorIsoIhom (J : CochainComplex C ℤ) [J.IsKInjective] :
    bifunctorHomQFunctor MonoidalClosed.internalHom J ≅
      (HomotopyCategory.quotient C _ ⋙ Qh).op ⋙
        MonoidalClosed.internalHom.flip.obj (Qh.obj ((HomotopyCategory.quotient C _).obj J)) :=
  NatIso.ofComponents
    (fun N ↦ @asIso _ _ _ _
      ((quotientCompQhIso C).inv.app (CochainComplex.internalHomObj N.unop J) ≫
        qhInternalHomToIhom N.unop J)
      (IsIso.comp_isIso' (Iso.isIso_inv ((quotientCompQhIso C).app _))
        (isIso_qhInternalHomToIhom N.unop J)))
    (fun {_ _} g ↦ qhInternalHomToIhom_naturality' g.unop J)

end DerivedCategory

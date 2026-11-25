/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedForgetTensorChainAssociativity

/-! # Associativity of normalized tensor chain models

Source: Stacks Project, Tags 0FPT and 06YU.
(blueprint: lem-sf-ringed-forget-model-chain-associativity).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false

universe b vb a va
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace CategoryTheory.RingedForgetTensorTransposition

/-- Native associator identifications give the associativity square for chain models.
Source: Stacks Project, Tags 0FPT and 06YU.
(blueprint: lem-sf-ringed-forget-model-chain-associativity)

Proof: replace the supplied model associators by the native associators using
their two identifications. The summand-normalized chain associativity theorem
then gives the required equation. Normalize the uncurried functor object
projections to identify its endpoints. Keeping this calculation abstract avoids
unfolding concrete sheaf tensor constructions. There is no derived localization
or flatness assertion. -/
theorem tensorComparison_model_chain_associativity
    {B : Type b} [Category.{vb} B] [Preadditive B] [HasZeroObject B]
    [MonoidalCategory B] [MonoidalPreadditive B]
    [∀ (X Y : GradedObject ℤ B), X.HasTensor Y]
    [∀ X, PreservesColimit (Functor.empty.{0} B) ((curriedTensor B).obj X)]
    [∀ X, PreservesColimit (Functor.empty.{0} B) ((curriedTensor B).flip.obj X)]
    [∀ (W X Y Z : GradedObject ℤ B), GradedObject.HasTensor₄ObjExt W X Y Z]
    [∀ (X Y Z : GradedObject ℤ B), GradedObject.HasGoodTensor₁₂Tensor X Y Z]
    [∀ (X Y Z : GradedObject ℤ B), GradedObject.HasGoodTensorTensor₂₃ X Y Z]
    {A : Type a} [Category.{va} A] [Preadditive A] [HasZeroObject A]
    [MonoidalCategory A] [MonoidalPreadditive A]
    [∀ (X Y : GradedObject ℤ A), X.HasTensor Y]
    [∀ X, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).obj X)]
    [∀ X, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).flip.obj X)]
    [∀ (W X Y Z : GradedObject ℤ A), GradedObject.HasTensor₄ObjExt W X Y Z]
    [∀ (X Y Z : GradedObject ℤ A), GradedObject.HasGoodTensor₁₂Tensor X Y Z]
    [∀ (X Y Z : GradedObject ℤ A), GradedObject.HasGoodTensorTensor₂₃ X Y Z]
    (F : B ⥤ A) [F.Additive]
    (ν : MonoidalCategory.tensor B ⋙ F ≅ (F.prod F) ⋙ MonoidalCategory.tensor A)
    (δ : Functor.uncurry.obj ((curriedTensor B).map₂CochainComplex) ⋙
        F.mapHomologicalComplex (.up ℤ) ≅
      ((F.mapHomologicalComplex (.up ℤ)).prod (F.mapHomologicalComplex (.up ℤ))) ⋙
        Functor.uncurry.obj ((curriedTensor A).map₂CochainComplex))
    (hδ : ∀ (P Q : CochainComplex B ℤ) (p q n : ℤ) (h : p + q = n),
      F.map (HomologicalComplex.ιTensorObj P Q p q n h) ≫ (δ.hom.app (P, Q)).f n =
        ν.hom.app (P.X p, Q.X q) ≫
          HomologicalComplex.ιTensorObj ((F.mapHomologicalComplex (.up ℤ)).obj P)
            ((F.mapHomologicalComplex (.up ℤ)).obj Q) p q n h)
    (hν : ∀ X Y Z : B,
      (ν.inv.app (X, Y) ▷ F.obj Z) ≫ ν.inv.app (X ⊗ Y, Z) ≫ F.map (α_ X Y Z).hom =
        (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom ≫
          (F.obj X ◁ ν.inv.app (Y, Z)) ≫ ν.inv.app (X, Y ⊗ Z))
    (P Q N : CochainComplex B ℤ)
    (aB : (Functor.uncurry.obj ((curriedTensor B).map₂CochainComplex)).obj
        ((Functor.uncurry.obj ((curriedTensor B).map₂CochainComplex)).obj (P, Q), N) ≅
      (Functor.uncurry.obj ((curriedTensor B).map₂CochainComplex)).obj
        (P, (Functor.uncurry.obj ((curriedTensor B).map₂CochainComplex)).obj (Q, N)))
    (aA : (Functor.uncurry.obj ((curriedTensor A).map₂CochainComplex)).obj
        ((Functor.uncurry.obj ((curriedTensor A).map₂CochainComplex)).obj
          ((F.mapHomologicalComplex (.up ℤ)).obj P, (F.mapHomologicalComplex (.up ℤ)).obj Q),
          (F.mapHomologicalComplex (.up ℤ)).obj N) ≅
      (Functor.uncurry.obj ((curriedTensor A).map₂CochainComplex)).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj P,
          (Functor.uncurry.obj ((curriedTensor A).map₂CochainComplex)).obj
            ((F.mapHomologicalComplex (.up ℤ)).obj Q, (F.mapHomologicalComplex (.up ℤ)).obj N)))
    (haB : aB.hom = (α_ P Q N).hom)
    (haA : aA.hom = (α_ ((F.mapHomologicalComplex (.up ℤ)).obj P)
      ((F.mapHomologicalComplex (.up ℤ)).obj Q)
      ((F.mapHomologicalComplex (.up ℤ)).obj N)).hom) :
    let V := F.mapHomologicalComplex (.up ℤ)
    let T_B := Functor.uncurry.obj ((curriedTensor B).map₂CochainComplex)
    let T_A := Functor.uncurry.obj ((curriedTensor A).map₂CochainComplex)
    V.map aB.hom ≫ δ.hom.app (P, T_B.obj (Q, N)) ≫
        T_A.map (X := (V.obj P, V.obj (T_B.obj (Q, N))))
          (Y := (V.obj P, T_A.obj (V.obj Q, V.obj N)))
          (𝟙 (V.obj P), δ.hom.app (Q, N)) =
      δ.hom.app (T_B.obj (P, Q), N) ≫
        T_A.map (X := (V.obj (T_B.obj (P, Q)), V.obj N))
          (Y := (T_A.obj (V.obj P, V.obj Q), V.obj N))
          (δ.hom.app (P, Q), 𝟙 (V.obj N)) ≫ aA.hom := by
  dsimp only
  rw [haB, haA]
  have h := tensorComparison_chain_associativity F ν δ hδ hν P Q N
  dsimp only [Functor.comp_obj, Functor.prod_obj, Functor.uncurry_obj_obj,
    Functor.map₂CochainComplex, Functor.map₂HomologicalComplex_obj_obj] at h ⊢
  exact h

end CategoryTheory.RingedForgetTensorTransposition

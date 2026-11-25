/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
import Mathlib.CategoryTheory.Limits.Preserves.Opposites
import Mathlib.CategoryTheory.Triangulated.Opposite.Functor
import WeilConjectures.CategoryTheory.GrothendieckDerivedBrownCohomologicalRepresentability

/-! # Grothendieck derived Brown right adjoint

Source: Stacks Project, Tag 0F5Y, Proposition 19.15.2,
`injectives-proposition-brown`.
(auxiliary; not a blueprint node)
-/

@[expose] public section

universe w uA vA uD vD

open CategoryTheory.Limits

namespace CategoryTheory

/-- An exact coproduct-preserving functor out of the unbounded derived category of a
Grothendieck abelian category has a right adjoint.
Source: Stacks Project, Tag 0F5Y, `injectives-proposition-brown`.
(auxiliary; not a blueprint node)

Proof in words: for each target object Y, the additive functor
H(W) = Hom(F(W), Y) is cohomological by exactness and takes coproducts to products.
The Grothendieck Brown argument represents H as follows. Present the abelian
category by the Gabriel-Popescu exact localization L from modules over a ring R.
Its derived right adjoint RG is fully faithful and L RG is the identity. The
functor H L is represented by a module complex E, by Brown representability for
the compact generator R. In the triangle M → E → RG(L(E)) → M[1], L(M) = 0,
so Hom(M, E) = H(L(M)) = 0. Thus E → RG(L(E)) is a split monomorphism.
Via the localization adjunction, H is consequently a natural direct summand of
Hom(-, L(E)). The derived category is idempotent complete, so this summand is
represented. Finally Yoneda assembles the representing objects for all Y into a
functor and the natural representing bijections give the right adjunction.
This is the argument of Tags 0F5X and 0F5Y; no compact-generation assertion for
D(A) is used.
-/
theorem grothendieckDerived_hasRightAdjoint
    {A : Type uA} [Category.{vA} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] [HasDerivedCategory.{w} A]
    {D : Type uD} [Category.{vD} D] [HasZeroObject D] [HasShift D ℤ]
    [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive]
    [Pretriangulated D] [IsTriangulated D]
    [HasCoproducts.{max w vA vD} D]
    (F : DerivedCategory A ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    [HasCoproducts.{max w vA vD} (DerivedCategory A)]
    (hF : ∀ I : Type (max w vA vD),
      PreservesColimitsOfShape (Discrete I) F) :
    F.IsLeftAdjoint := by
  let := Pretriangulated.Opposite.instHasShiftOppositeInt (DerivedCategory A)
  let := Pretriangulated.Opposite.instHasShiftOppositeInt D
  let := Pretriangulated.Opposite.instOpposite (C := DerivedCategory A)
  let := Pretriangulated.Opposite.instOpposite (C := D)
  let := Pretriangulated.Opposite.commShiftFunctorOpInt F
  let := Pretriangulated.Opposite.functor_isTriangulated_op F
  apply Functor.isLeftAdjoint_of_rightAdjointObjIsDefined_eq_top
  funext Y
  apply propext
  change (F.op ⋙ yoneda.obj Y).IsRepresentable ↔ True
  refine ⟨fun _ ↦ trivial, fun _ ↦ ?_⟩
  let H := F.op ⋙ preadditiveYoneda.obj Y
  have hH : ∀ I : Type (max w vA vD), PreservesLimitsOfShape (Discrete I) H := by
    intro I
    let := hF I
    let : PreservesColimitsOfShape (Discrete I)ᵒᵖ F :=
      preservesColimitsOfShape_of_equiv (Discrete.opposite I).symm F
    let : PreservesLimitsOfShape (Discrete I) F.op :=
      preservesLimitsOfShape_op (Discrete I) F
    have : PreservesLimitsOfShape (Discrete I)
        (preadditiveYoneda.obj Y ⋙ forget AddCommGrpCat) :=
      inferInstanceAs (PreservesLimitsOfShape (Discrete I) (yoneda.obj Y))
    have : PreservesLimitsOfShape (Discrete I) (preadditiveYoneda.obj Y) :=
      preservesLimitsOfShape_of_reflects_of_preserves _ (forget AddCommGrpCat)
    change PreservesLimitsOfShape (Discrete I) (F.op ⋙ preadditiveYoneda.obj Y)
    infer_instance
  have : H.IsHomological := by
    change (F.op ⋙ preadditiveYoneda.obj Y).IsHomological
    infer_instance
  exact grothendieckDerived_cohomological_isRepresentable H hH

end CategoryTheory

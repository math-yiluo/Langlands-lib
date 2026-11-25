/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbedding.GabrielPopescu
public import WeilConjectures.CategoryTheory.DerivedCategory.BrownRepresentability.ModuleCat
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
public import WeilConjectures.CategoryTheory.Triangulated.BrownRepresentability.Localization

/-!
# Brown representability for the derived category of a Grothendieck abelian category

Let `A` be a Grothendieck abelian category. We show that every triangulated functor
`F : D(A) ⥤ T` which preserves coproducts has a right adjoint
(`DerivedCategory.isLeftAdjoint_of_preservesCoproducts`, Stacks Proposition 19.15.2, Tag 0F5Y).

## The proof (Stacks Lemma 19.15.1)

Let `G` be a separator of `A` and `R = (End G)ᵐᵒᵖ`. By the Gabriel-Popescu theorem, the functor
`U = Hom(G, -) : A ⥤ ModuleCat R` is fully faithful and has an exact left adjoint `T = - ⊗ G`.
Hence `Φ = D(T) : D(R) ⥤ D(A)` is a triangulated functor, left adjoint to the right derived
functor `Ψ = RU`, which is fully faithful as `U` is fully faithful and preserves K-injective
complexes. The functor `Φ ⋙ F : D(R) ⥤ T` is triangulated and preserves coproducts, so it has a
right adjoint by Brown representability for `D(R)`
(`DerivedCategory.isLeftAdjoint_of_preservesCoproducts_moduleCat`), and then so does `F`
(`CategoryTheory.Functor.isLeftAdjoint_of_isLeftAdjoint_comp`).

This is the homological input of the blueprint node
`theorem-existence-exceptional-inverse-image--1`.
-/

@[expose] public section

universe v u u'

open CategoryTheory Limits Abelian IsGrothendieckAbelian

namespace DerivedCategory

variable {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
  [HasDerivedCategory.{v} A]

/-- **Brown representability for the derived category of a Grothendieck abelian category**
(Stacks Proposition 19.15.2, Tag 0F5Y; blueprint `theorem-existence-exceptional-inverse-image--1`):
a triangulated functor `F : D(A) ⥤ T` which preserves coproducts is a left adjoint. -/
theorem isLeftAdjoint_of_preservesCoproducts {T : Type u'} [Category.{v} T] [Preadditive T]
    [HasZeroObject T] [HasShift T ℤ] [∀ n : ℤ, (shiftFunctor T n).Additive] [Pretriangulated T]
    (F : DerivedCategory A ⥤ T) [F.CommShift ℤ] [F.IsTriangulated]
    [∀ J : Type v, PreservesColimitsOfShape (Discrete J) F] : F.IsLeftAdjoint := by
  let G : A := separator A
  have hG : IsSeparator G := isSeparator_separator A
  let adj := tensorObjPreadditiveCoyonedaObjAdjunction G
  have : (tensorObj G).Additive := adj.left_adjoint_additive
  have : PreservesFiniteLimits (tensorObj G) := GabrielPopescu.preservesFiniteLimits G hG
  have : (preadditiveCoyonedaObj G).Full := GabrielPopescu.full G hG
  have : (preadditiveCoyonedaObj G).Faithful :=
    (isSeparator_iff_faithful_preadditiveCoyonedaObj G).1 hG
  have : (preadditiveCoyonedaObj G).PreservesKInjectiveComplexes :=
    adj.preservesKInjectiveComplexes
  let adjD := adj.mapDerivedCategoryRightDerivedAdjunction
  have : (tensorObj G).mapDerivedCategory.IsLeftAdjoint := adjD.isLeftAdjoint
  have : ∀ J : Type v, PreservesColimitsOfShape (Discrete J)
      ((tensorObj G).mapDerivedCategory ⋙ F) := fun J ↦ inferInstance
  have : ((tensorObj G).mapDerivedCategory ⋙ F).IsLeftAdjoint :=
    isLeftAdjoint_of_preservesCoproducts_moduleCat _
  exact Functor.isLeftAdjoint_of_isLeftAdjoint_comp adjD F

end DerivedCategory

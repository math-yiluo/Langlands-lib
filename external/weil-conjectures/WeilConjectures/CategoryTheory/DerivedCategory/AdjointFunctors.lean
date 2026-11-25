/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import WeilConjectures.CategoryTheory.DerivedCategory.EverywhereDefinedDerivedFunctors

/-!
# Everywhere defined derived functors of an adjoint pair

Source: Stacks Project, Derived Categories, Lemma 09T5, Lemma 0DVC and Definition 05S9
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe wA wB vA vB uA uB

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Adjunction

/-- Stacks Project, Lemma 09T5, with "defined at" in the sense of Definition 05S9
(auxiliary; not a blueprint node).

The hypotheses state that the quasi-isomorphism denominator ind-diagram and pro-diagram
are essentially constant with some value (def-pc-essentially-constant-ind-diagram,
def-pc-essentially-constant-pro-diagram; Categories Tag 05PU); that value is RF(K), resp.
LG(M). The denominator morphisms are all commuting triangles
(`⊤`), not just quasi-isomorphisms. No injectives, projectives, boundedness or absoluteness
hypothesis is imposed.

The conclusion supplies the total derived functors and their comparison transformations.
The derived adjunction's `homEquiv` is the natural bijection in the statement. The final
identity specifies its canonical compatibility with the original adjunction on homotopy
categories, rather than allowing an unrelated adjunction.

Proof:
1. Apply `lem-pc-pre-derived-adjoint-functors-general` (Stacks Lemma 0DVC) at each pair of
complexes. Essential constancy gives its hypotheses and hence the canonical Hom bijection;
invert the bijection there to obtain Hom(LG(M), K) ≃ Hom(M, RF(K)).
2. By Definition 05S9 and Lemma 05SA, everywhere defined values assemble into total derived
functors with the universal comparison transformations. The bifunctoriality in
`lem-pc-pre-derived-adjoint-functors-general` makes the bijections an adjunction. The
construction from the underived adjunction yields the displayed compatibility identity. -/
theorem exists_derived_adjunction_of_essentially_constant
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    (F : A ⥤ B) (G : B ⥤ A) [F.Additive] [G.Additive] (adj : G ⊣ F)
    (hR : ∀ K : HomotopyCategory A (ComplexShape.up ℤ),
      let W := HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
      let D := MorphismProperty.Under.forget W ⊤ K ⋙ Under.forget K ⋙
        F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh
      ∃ X : DerivedCategory B, IsEssentiallyConstantIndDiagram D X)
    (hL : ∀ M : HomotopyCategory B (ComplexShape.up ℤ),
      let W := HomotopyCategory.quasiIso B (ComplexShape.up ℤ)
      let D := MorphismProperty.Over.forget W ⊤ M ⋙ Over.forget M ⋙
        G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh
      ∃ X : DerivedCategory A, IsEssentiallyConstantProDiagram D X) :
    ∃ (RF : DerivedCategory A ⥤ DerivedCategory B)
      (LG : DerivedCategory B ⥤ DerivedCategory A)
      (β : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
        DerivedCategory.Qh ⋙ RF)
      (α : DerivedCategory.Qh ⋙ LG ⟶
        G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh),
      RF.IsRightDerivedFunctor β (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ∧
      LG.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso B (ComplexShape.up ℤ)) ∧
      ∃ d : LG ⊣ RF,
        ∀ (M : HomotopyCategory B (ComplexShape.up ℤ))
          (K : HomotopyCategory A (ComplexShape.up ℤ))
          (f : (G.mapHomotopyCategory (ComplexShape.up ℤ)).obj M ⟶ K),
          d.homEquiv (DerivedCategory.Qh.obj M) (DerivedCategory.Qh.obj K)
            (α.app M ≫ DerivedCategory.Qh.map f) =
          DerivedCategory.Qh.map ((adj.mapHomotopyCategory (ComplexShape.up ℤ)).homEquiv M K f)
            ≫ β.app K := by
  obtain ⟨RF, LG, β, α, hRF, hLG⟩ :=
    exists_everywhere_defined_derived_functors F G hR hL
  obtain ⟨d, hd⟩ := exists_derived_adjunction_compatibility F G adj hR hL RF LG β α hRF hLG
  exact ⟨RF, LG, β, α, hRF, hLG, d, hd⟩

end CategoryTheory.Adjunction

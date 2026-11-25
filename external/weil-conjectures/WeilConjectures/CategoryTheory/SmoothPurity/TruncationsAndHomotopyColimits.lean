/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Embedding.StupidTrunc
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.Triangulated
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.CategoryTheory.TruncationTriangle
public import WeilConjectures.CategoryTheory.TruncationCouple
public import WeilConjectures.CategoryTheory.ProperBaseChange.HypercohomologyFiltrations
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.AlgebraicGeometry.GeometricStalkColimits

/-!
# Truncations and homotopy colimits

Source: Weil conjectures blueprint, chap-Smooth-purity, proposition-ordinary-external-kunneth--1,
node proposition-open-direct-image-preserves-finite, order 1690 (blueprint:
proposition-open-direct-image-preserves-finite).

The existing constructions are used without defining them a second time:

* Stupid truncations are `K.stupidTrunc (ComplexShape.embeddingUpIntGE n)` and
  `K.stupidTrunc (ComplexShape.embeddingUpIntLE n)`. Restriction followed by extension
  by zero retains exactly the indicated terms and internal differentials.
* Good truncations are `K.truncLE n` and `K.truncGE n`, with boundary objects
  `K.cycles n` and `K.opcycles n`. The maps are `CochainComplex.truncLEMap` and
  `CochainComplex.truncGEMap`. On the derived category they are the truncations of
  `DerivedCategory.TStructure.t`. Stupid truncations are used only on complexes.
* `DerivedCategory.truncation_triangle` supplies the successive distinguished triangle.
  `CategoryTheory.truncationCouple` supplies its bounded-below derived exact-couple
  construction; `AlgebraicGeometry.Etale.hypercohomologyFiltrations` gives the three
  filtrations in the cartesian-square setting. The single triangle is not the couple.
* For `J = T.smallEtaleTopology`, the sheaf colimit of `F` is the sheafification
  `(presheafToSheaf J AddCommGrpCat).obj (colimit (F ⋙ sheafToPresheaf J AddCommGrpCat))`.
  Presheaf colimits are objectwise. `CategoryTheory.moduleSheaves_colimits_forgetful`
  gives the module-presheaf version and preservation by the underlying abelian sheaf.
* The pointed neighbourhood category is `(Scheme.pointSmallEtale s).fiber.Elements`.
  Its opposite is filtered, and `(Scheme.pointSmallEtale s).sheafFiber` is the stalk,
  computed by the colimit over this opposite. `Scheme.geometricStalk_preservesColimits`
  gives preservation on abelian sheaves (encoded there as integer modules) and on
  cochain complexes. Module sheaves use the preceding forgetful-functor result.

The new definition below records precisely the telescope triangle, without choosing
cones, or asserting a functorial choice. Its coproduct is Mathlib's colimit of a
`Discrete ℕ` diagram. Mathlib's shifts use `(K[1])^i = K^(i+1)` and the negative differential.
-/

@[expose] public section

universe v u

open CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory

/-- A sequential homotopy colimit is any cone object in the distinguished triangle
`B --(1 - s)--> B --> H --> B[1]`, where `B` is the countable coproduct of `E j`
and `s` is determined by `Sigma.ι E j ≫ s = u j ≫ Sigma.ι E (j + 1)`.
The two remaining arrows are existentially quantified: no cone or functorial choice
is part of the definition. Source: blueprint chap-Smooth-purity,
proposition-ordinary-external-kunneth--1, node order 1690 (blueprint:
proposition-open-direct-image-preserves-finite). -/
def IsSequentialHomotopyColimit
    {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
    [HasCountableCoproducts C] (E : ℕ → C) (u : ∀ j : ℕ, E j ⟶ E (j + 1))
    (H : C) : Prop :=
  ∃ (g : (∐ E) ⟶ H) (h : H ⟶ (∐ E)⟦(1 : ℤ)⟧),
    Triangle.mk (𝟙 (∐ E) - Sigma.desc (fun j : ℕ ↦ u j ≫ Sigma.ι E (j + 1))) g h ∈
      distTriang C

end CategoryTheory

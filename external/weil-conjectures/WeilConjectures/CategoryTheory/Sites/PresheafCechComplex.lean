/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.AlgebraicTopology.CechNerve
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Category.Grp.Abelian

/-!
# Čech cochains using products of presheaves

Source: Stacks Project, Cohomology on Sites, Tags 03AK, 03AS, 03AT.
(blueprint: def-sc-presheaf-cech-complex)
-/

@[expose] public section

universe u v

open CategoryTheory

namespace CategoryTheory

/-- The Čech cochain complex obtained by applying free abelian presheaves and Hom
into `F` to the nerve of a map of presheaves of sets. All fibre products are taken
in the presheaf category, so the original category need not have pullbacks.
Source: Stacks Project, Cohomology on Sites, Tags 03AK and 03AS, with the nerve
formed in presheaves as in Hypercoverings, Tag 01GC.
(blueprint: def-sc-presheaf-cech-complex) -/
noncomputable def presheafCechComplex {C : Type u} [Category.{v} C]
    (f : Arrow (Cᵒᵖ ⥤ Type v)) (F : Cᵒᵖ ⥤ AddCommGrpCat.{v}) :
    CochainComplex AddCommGrpCat.{max u v} ℕ :=
  (AlgebraicTopology.alternatingCofaceMapComplex _).obj
    ((f.cechNerve ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free).rightOp ⋙
      preadditiveYoneda.obj F)

end CategoryTheory

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Additive

/-! # A square of additive functors lifted to iterated complex functors

Source: the functorial construction of complexes, Stacks Tag 010V.
-/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory
namespace CategoryTheory.ConstantCompletion

/-- Lift a square while retaining its two iterated complex functors as endpoints.
Source: Stacks Tag 010V (blueprint: def-sf-complex-functor-square). -/
@[irreducible]
def mapComplexSquare
    {C D D' E : Type*} [Category C] [Category D] [Category D'] [Category E]
    [Preadditive C] [Preadditive D] [Preadditive D'] [Preadditive E]
    (F : C ⥤ D) (G : D ⥤ E) (F' : C ⥤ D') (G' : D' ⥤ E)
    [F.Additive] [G.Additive] [F'.Additive] [G'.Additive]
    (e : F ⋙ G ≅ F' ⋙ G') :
    F.mapHomologicalComplex (.up ℤ) ⋙ G.mapHomologicalComplex (.up ℤ) ≅
      F'.mapHomologicalComplex (.up ℤ) ⋙ G'.mapHomologicalComplex (.up ℤ) :=
  NatIso.mapHomologicalComplex e (.up ℤ)

end CategoryTheory.ConstantCompletion

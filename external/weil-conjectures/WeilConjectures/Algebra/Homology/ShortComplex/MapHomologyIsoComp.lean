/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# The homology isomorphism of a composite functor

For functors `A : C ⥤ D` and `B : D ⥤ E` preserving the homology of a short complex `S`, the
canonical isomorphism `(S.map (A ⋙ B)).homology ≅ B (A S.homology)` is the composite of those
of `A` and `B` (`CategoryTheory.ShortComplex.mapHomologyIso_comp`).
-/

@[expose] public section

namespace CategoryTheory.ShortComplex

open Category Limits

variable {C D E : Type*} [Category C] [Category D] [Category E] [HasZeroMorphisms C]
  [HasZeroMorphisms D] [HasZeroMorphisms E] [CategoryWithHomology C] [CategoryWithHomology D]
  [CategoryWithHomology E] (S : ShortComplex C) (A : C ⥤ D) (B : D ⥤ E)
  [A.PreservesZeroMorphisms] [B.PreservesZeroMorphisms]
  [A.PreservesLeftHomologyOf S] [B.PreservesLeftHomologyOf (S.map A)]
  [(A ⋙ B).PreservesLeftHomologyOf S]

/-- The homology isomorphism of a composite functor is the composite of the homology
isomorphisms. -/
lemma mapHomologyIso_comp :
    S.mapHomologyIso (A ⋙ B) =
      (S.map A).mapHomologyIso B ≪≫ B.mapIso (S.mapHomologyIso A) := by
  have key : (S.homologyData.left.map (A ⋙ B)).homologyIso =
      ((S.homologyData.left.map A).map B).homologyIso := by
    ext
    rw [← cancel_epi ((S.map A).map B).homologyπ,
      LeftHomologyData.homologyπ_comp_homologyIso_hom,
      LeftHomologyData.homologyπ_comp_homologyIso_hom]
    congr 1
    rw [← cancel_mono ((S.homologyData.left.map A).map B).i,
      LeftHomologyData.cyclesIso_hom_comp_i]
    exact (S.homologyData.left.map (A ⋙ B)).cyclesIso_hom_comp_i
  rw [S.homologyData.left.mapHomologyIso_eq (A ⋙ B), S.homologyData.left.mapHomologyIso_eq A,
    (S.homologyData.left.map A).mapHomologyIso_eq B, key]
  ext
  simp

end CategoryTheory.ShortComplex

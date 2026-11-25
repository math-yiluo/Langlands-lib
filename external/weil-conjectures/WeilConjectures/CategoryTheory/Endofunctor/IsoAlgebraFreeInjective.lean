/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebra

/-!
# Summands of free algebras on injective objects

For an autoequivalence `F` of a category `C` and an injective object `S`, the summands `Fⁿ S` of
the free algebra `∐ₙ Fⁿ S` are injective
(`CategoryTheory.Endofunctor.IsoAlgebra.Free.injective_obj`). We also record that a functor
preserving zero morphisms preserves strictly bounded below cochain complexes
(`CochainComplex.isStrictlyGE_mapHomologicalComplex_obj`).
-/

@[expose] public section

open CategoryTheory Limits

namespace CochainComplex

variable {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]

/-- A functor preserving zero morphisms sends cochain complexes that are strictly `≥ n` to
cochain complexes that are strictly `≥ n`. -/
instance isStrictlyGE_mapHomologicalComplex_obj (G : C ⥤ D) [G.PreservesZeroMorphisms]
    (K : CochainComplex C ℤ) (n : ℤ) [K.IsStrictlyGE n] :
    CochainComplex.IsStrictlyGE ((G.mapHomologicalComplex (.up ℤ)).obj K) n :=
  (isStrictlyGE_iff _ n).2 fun i hi ↦ G.map_isZero (K.isZero_of_isStrictlyGE n i hi)

end CochainComplex

namespace CategoryTheory.Endofunctor.IsoAlgebra.Free

variable {C : Type*} [Category* C] (F : C ⥤ C) [F.IsEquivalence]

/-- The summands `Fⁿ S` of the free algebra on an injective object `S` are injective. -/
instance injective_obj (S : C) [Injective S] (n : ℤ) : Injective (obj F S n) := by
  have hpos (n : ℕ) : Injective (posObj F S n) := by
    induction n with
    | zero => assumption
    | succ n ih => exact F.injective_obj (posObj F S n)
  have hneg (n : ℕ) : Injective (negObj F S n) := by
    induction n with
    | zero => exact F.inv.injective_obj S
    | succ n ih => exact F.inv.injective_obj (negObj F S n)
  rcases n with n | n
  · exact hpos n
  · exact hneg n

end CategoryTheory.Endofunctor.IsoAlgebra.Free

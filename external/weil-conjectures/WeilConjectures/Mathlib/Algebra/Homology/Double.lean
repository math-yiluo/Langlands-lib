/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.Double

/-!
# Morphisms out of the corepresentative of `K ↦ (X ⟶ K.X j)`

Let `c : ComplexShape ι` be a complex shape with no loop. For `X : C` and `j : ι`, the
functor which sends `K : HomologicalComplex C c` to `X ⟶ K.X j` is corepresented by
`HomologicalComplex.evalCompCoyonedaCorepresentative c X j`. In this file, we introduce the
tautological morphism
`evalCompCoyonedaUnit c X j : X ⟶ (evalCompCoyonedaCorepresentative c X j).X j`
which corresponds to the identity, and observe that the morphism of complexes attached to an
epimorphism `q : X ⟶ K.X j` is an epimorphism in degree `j`.
-/

@[expose] public section

universe v u

open CategoryTheory Category Limits Opposite

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
  {ι : Type*} (c : ComplexShape ι) [c.HasNoLoop] (X : C) (j : ι)

/-- The tautological morphism `X ⟶ (evalCompCoyonedaCorepresentative c X j).X j`, i.e. the
element corresponding to the identity under the corepresentability of `K ↦ (X ⟶ K.X j)`. -/
noncomputable def evalCompCoyonedaUnit :
    X ⟶ (evalCompCoyonedaCorepresentative c X j).X j :=
  (evalCompCoyonedaCorepresentable c X j).homEquiv (𝟙 _)

variable {c X j}

lemma evalCompCoyonedaUnit_comp {K : HomologicalComplex C c}
    (φ : evalCompCoyonedaCorepresentative c X j ⟶ K) :
    evalCompCoyonedaUnit c X j ≫ φ.f j =
      (evalCompCoyonedaCorepresentable c X j).homEquiv φ := by
  simpa [evalCompCoyonedaUnit] using
    ((evalCompCoyonedaCorepresentable c X j).homEquiv_comp φ (𝟙 _)).symm

lemma epi_f_homEquiv_symm {K : HomologicalComplex C c} (q : X ⟶ K.X j) [Epi q] :
    Epi (((evalCompCoyonedaCorepresentable c X j).homEquiv.symm q).f j) := by
  have h : evalCompCoyonedaUnit c X j ≫
      ((evalCompCoyonedaCorepresentable c X j).homEquiv.symm q).f j = q := by
    rw [evalCompCoyonedaUnit_comp, Equiv.apply_symm_apply]
  have : Epi (evalCompCoyonedaUnit c X j ≫
      ((evalCompCoyonedaCorepresentable c X j).homEquiv.symm q).f j) := by
    rw [h]; infer_instance
  exact epi_of_epi (evalCompCoyonedaUnit c X j) _

end HomologicalComplex

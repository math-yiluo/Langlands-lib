/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.Embedding.HomEquiv
public import Mathlib.Algebra.Homology.Embedding.IsSupported

/-!
# A complex supported on an embedding is the extension of its restriction

If `K : HomologicalComplex C c'` is strictly supported on an embedding `e : c.Embedding c'`, the
canonical morphism `K ⟶ (K.restriction e).extend e` (the lift of the identity of
`K.restriction e`) is an isomorphism.
-/

@[expose] public section

open CategoryTheory Limits

namespace HomologicalComplex

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]
  (K : HomologicalComplex C c') (e : c.Embedding c') [e.IsRelIff] [K.IsStrictlySupported e]

omit [HasZeroObject C] in
lemma hasLift_restriction_id : e.HasLift (𝟙 (K.restriction e)) := by
  intro j hj i' hi'
  have : ¬ ∃ i, e.f i = i' := fun ⟨i, hi⟩ ↦ hj.notMem hi' i hi
  exact (K.isZero_X_of_isStrictlySupported e i' (by simpa using this)).eq_of_src _ _

/-- A complex strictly supported on an embedding `e` is isomorphic to the extension of its
restriction along `e`. -/
noncomputable def isoRestrictionExtend : K ≅ (K.restriction e).extend e :=
  have : IsIso (e.liftExtend (𝟙 (K.restriction e)) (hasLift_restriction_id K e)) := by
    have (i' : ι') : IsIso ((e.liftExtend _ (hasLift_restriction_id K e)).f i') := by
      by_cases h : ∃ i, e.f i = i'
      · obtain ⟨i, hi⟩ := h
        rw [e.isIso_liftExtend_f_iff _ _ hi]
        dsimp
        infer_instance
      · exact isIso_of_source_target_iso_zero _
          (K.isZero_X_of_isStrictlySupported e i' (by simpa using h)).isoZero
          (((K.restriction e).isZero_extend_X e i' (by simpa using h))).isoZero
    exact Hom.isIso_of_components _
  asIso (e.liftExtend (𝟙 (K.restriction e)) (hasLift_restriction_id K e))

end HomologicalComplex

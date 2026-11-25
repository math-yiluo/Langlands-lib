/-
Copyright (c) 2026 The Weil Conjectures Project Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero

/-!
# Properties of the terms of an extended complex

If all terms of `K` satisfy a property `P` which contains zero objects and is closed under
isomorphisms, then so do all terms of `K.extend e`.
-/

@[expose] public section

namespace HomologicalComplex

open CategoryTheory Limits

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]

/-- If `P` contains zero objects and is closed under isomorphisms and all terms of `K` satisfy
`P`, then all terms of `K.extend e` satisfy `P`. -/
lemma prop_extend_X (P : ObjectProperty C) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    {K : HomologicalComplex C c} (e : c.Embedding c') (hK : ∀ i, P (K.X i)) (i' : ι') :
    P ((K.extend e).X i') := by
  by_cases h : ∃ i, e.f i = i'
  · obtain ⟨i, hi⟩ := h
    exact P.prop_of_iso (K.extendXIso e hi).symm (hK i)
  · exact P.prop_of_isZero (K.isZero_extend_X e i' (by simpa using h))

end HomologicalComplex

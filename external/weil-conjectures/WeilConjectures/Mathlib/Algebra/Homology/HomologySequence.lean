/-
Copyright (c) 2026 The Weil Conjectures Project Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.HomologySequence
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# The short exact sequences of cycles of an exact complex

If a homological complex `K` is exact at `j` and `c.Rel i j`, then
`0 ⟶ K.cycles i ⟶ K.X i ⟶ K.cycles j ⟶ 0` is a short exact sequence.
-/

@[expose] public section

namespace HomologicalComplex

open CategoryTheory Limits

variable {C : Type*} [Category* C] [Abelian C] {ι : Type*} {c : ComplexShape ι}
  {K : HomologicalComplex C c}

/-- If `K` is exact at `j` and `c.Rel i j`, then
`0 ⟶ K.cycles i ⟶ K.X i ⟶ K.cycles j ⟶ 0` is a short exact sequence. -/
lemma ExactAt.shortExact_cyclesShortComplex {i j : ι} (hj : K.ExactAt j) (hij : c.Rel i j) :
    (K.cyclesShortComplex i j).ShortExact := by
  have := hj.epi_toCycles i (c.prev_eq' hij)
  refine ShortComplex.ShortExact.mk' ?_ (inferInstanceAs (Mono (K.iCycles i))) this
  let φ : K.cyclesShortComplex i j ⟶ ShortComplex.mk _ _ (K.iCycles_d i j) :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := K.iCycles j }
  rw [ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ]
  exact ShortComplex.exact_of_f_is_kernel _ (K.cyclesIsKernel i j (c.next_eq' hij))

end HomologicalComplex

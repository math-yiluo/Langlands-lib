import Langlands.Algebra.IdealFiniteGenerationFromQuotientStabilityStatement

/-! # Finite generation from stability of finite quotient approximations -/

universe u v

namespace Langlands.Algebra

/-- The elementary finite-generation step extracted from Stacks tag 05UV. -/
theorem idealFiniteGenerationFromQuotientStability :
    IdealFiniteGenerationFromQuotientStabilityStatement.{u, v} := by
  classical
  intro B F _ _ f J hfg hstable
  obtain ⟨s, hs, hspan⟩ :=
    (Submodule.fg_span_iff_fg_span_finset_subset (f '' (J : Set B))).mp hfg
  obtain ⟨t, htJ, htfin, htmap⟩ :=
    Set.exists_subset_image_finite_and.mp
      (show ∃ s : Set F, s ⊆ f '' (J : Set B) ∧ s.Finite ∧
          Ideal.span s = J.map f from
        ⟨s, hs, s.finite_toSet, hspan.symm⟩)
  let I : Ideal B := Ideal.span t
  have hIFG : I.FG := Submodule.fg_span htfin
  have hIJ : I ≤ J := Ideal.span_le.mpr htJ
  have hmap : I.map f = J.map f := (Ideal.map_span f t).trans htmap
  have hJI : J ≤ I := by
    intro x hx
    let K : Ideal B := I ⊔ Ideal.span {x}
    have hKFG : K.FG := Submodule.FG.sup hIFG (Submodule.fg_span_singleton x)
    have hIK : I ≤ K := le_sup_left
    have hKJ : K ≤ J := sup_le hIJ (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hx))
    have hxK : x ∈ K :=
      (show Ideal.span {x} ≤ K from le_sup_right) (Ideal.subset_span (Set.mem_singleton x))
    have hinj := hstable I K hIFG hKFG hIK hKJ hmap
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply hinj
    rw [Ideal.Quotient.factor_mk, map_zero, Ideal.Quotient.eq_zero_iff_mem]
    exact hxK
  exact (le_antisymm hIJ hJI) ▸ hIFG

end Langlands.Algebra

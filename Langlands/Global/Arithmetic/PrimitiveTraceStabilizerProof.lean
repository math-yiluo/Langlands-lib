import Langlands.Global.Arithmetic.PrimitiveTraceStabilizerStatement

/-!
# Exact trace-functional stabilizers from primitive coefficients
-/

noncomputable section

universe u v

namespace Langlands.Global

private theorem trace_precomposition_iff_fixed
    {F : Type u} {M : Type v} [Field F] [Field M]
    [Algebra F M] [FiniteDimensional F M] [Algebra.IsSeparable F M]
    (a : M) (σ : M ≃ₐ[F] M) :
    (∀ x : M, Algebra.trace F M (a * σ x) = Algebra.trace F M (a * x)) ↔
      σ a = a := by
  constructor
  · intro h
    have hdiff : a - σ a = 0 := by
      apply (traceForm_nondegenerate F M).1 (a - σ a)
      intro x
      rw [Algebra.traceForm_apply, sub_mul, map_sub]
      apply sub_eq_zero.mpr
      have hinv :
          Algebra.trace F M (σ a * x) =
          Algebra.trace F M (a * σ.symm x) := by
        simpa only [map_mul, σ.apply_symm_apply] using
          Algebra.trace_eq_of_algEquiv σ (a * σ.symm x)
      have hpre :
          Algebra.trace F M (a * x) =
          Algebra.trace F M (a * σ.symm x) := by
        simpa only [σ.apply_symm_apply] using h (σ.symm x)
      exact hpre.trans hinv.symm
    exact (sub_eq_zero.mp hdiff).symm
  · intro h x
    simpa only [map_mul, h] using Algebra.trace_eq_of_algEquiv σ (a * x)

private theorem primitive_trace_exact
    {F : Type u} {M : Type v} [Field F] [Field M]
    [Algebra F M] [FiniteDimensional F M] [Algebra.IsSeparable F M]
    (L : IntermediateField F M) (a : L)
    (hgen : IntermediateField.adjoin F ({a} : Set L) = ⊤) :
    HasExactTraceStabilizer L a := by
  intro σ
  rw [trace_precomposition_iff_fixed]
  constructor
  · intro h
    have hgenM : IntermediateField.adjoin F ({(a : M)} : Set M) = L := by
      simpa only [IntermediateField.lift_adjoin_simple, IntermediateField.lift_top] using
        congrArg IntermediateField.lift hgen
    have hhom : σ.toAlgHom.comp L.val = L.val := by
      apply IntermediateField.algHom_ext_of_eq_adjoin F hgenM.symm
      intro x hx
      have hx' : x = (a : M) := Set.mem_singleton_iff.mp hx
      subst x
      exact h
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact DFunLike.congr_fun hhom (⟨x, hx⟩ : L)
  · intro h
    exact (IntermediateField.mem_fixingSubgroup_iff L σ).mp h (a : M) a.property

/-- A primitive coefficient realizes the exact trace-functional stabilizer. -/
theorem primitiveTraceStabilizer : PrimitiveTraceStabilizerStatement.{u, v} := by
  intro F M _ _ _ _ _ L
  obtain ⟨a, hgen⟩ := Field.exists_primitive_element F L
  have hex : ∃ b : L, b ≠ 0 ∧ IntermediateField.adjoin F ({b} : Set L) = ⊤ := by
    by_cases hzero : a = 0
    · refine ⟨1, one_ne_zero, ?_⟩
      have hbot : (⊥ : IntermediateField F L) = ⊤ := by
        simpa only [hzero, IntermediateField.adjoin_zero] using hgen
      simpa only [IntermediateField.adjoin_one] using hbot
    · exact ⟨a, hzero, hgen⟩
  obtain ⟨b, hb, hgenb⟩ := hex
  exact ⟨b, hb, hgenb, primitive_trace_exact L b hgenb⟩

end Langlands.Global

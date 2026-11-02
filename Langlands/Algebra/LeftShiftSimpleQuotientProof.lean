import Langlands.Algebra.PrincipalLeftIdealProperProof

/-!
# Renard B.III: a simple quotient separating a shifted element

For a nonzero scalar shift with no left inverse, choose a maximal left ideal
containing its proper principal left ideal. The resulting simple quotient is
separated by the class of `1`.
-/

universe u

namespace Langlands.Renard

/-- Renard B.III's quotient argument, with the simple module realized as an
actual quotient by a maximal left ideal and separating vector the class of `1`. -/
theorem leftShiftSimpleQuotient (A : Type u) [Ring A] [Algebra ℂ A] :
    LeftShiftSimpleQuotientStatement A := by
  intro a z hz hleft
  have hproper : Submodule.span A {a - algebraMap ℂ A z} ≠ ⊤ :=
    (principalLeftIdealProper A (a - algebraMap ℂ A z)).2 hleft
  obtain ⟨I, hI, hle⟩ := Ideal.exists_le_maximal _ hproper
  have ha : a ∉ I := by
    intro ha
    have hshift : a - algebraMap ℂ A z ∈ I :=
      hle (Submodule.mem_span_singleton_self _)
    have hzI : algebraMap ℂ A z ∈ I := by
      simpa only [sub_sub_cancel] using I.sub_mem ha hshift
    have hone : (1 : A) ∈ I := by
      have h := I.smul_mem (algebraMap ℂ A z⁻¹) hzI
      simpa only [smul_eq_mul, ← map_mul, inv_mul_cancel₀ hz, map_one] using h
    exact hI.ne_top ((Ideal.eq_top_iff_one I).2 hone)
  refine ⟨I, hI.out, hle, isSimpleModule_iff_isCoatom.mpr hI.out, ?_⟩
  have hact : a • I.mkQ 1 = I.mkQ a := by
    rw [← LinearMap.map_smul, smul_eq_mul, mul_one]
  rwa [hact, Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]

end Langlands.Renard

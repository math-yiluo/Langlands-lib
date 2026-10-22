import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.Finiteness.Basic

/-! # Continuity of homomorphisms out of finite Banach algebras -/

noncomputable section

open Topology

universe u v w z

namespace Langlands.Analytic.FiniteBanachAlgebra

variable {K : Type u} [NontriviallyNormedField K]
  {A : Type v} [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A]
  {B : Type w} [NormedCommRing B] [NormedAlgebra K B] [CompleteSpace B]
  [Algebra A B] [IsScalarTower K A B] [Module.Finite A B]
  {C : Type z} [NormedCommRing C] [Algebra A C]

include K

/-- An algebra homomorphism out of a finite Banach algebra is continuous
when its restriction to the coefficient algebra is continuous. The
finite generating family and the quotient map are constructed in the
proof; continuity of the full homomorphism is not assumed. -/
theorem continuous_algHom (f : B →ₐ[A] C)
    (hAB : Continuous (algebraMap A B)) (hAC : Continuous (algebraMap A C)) :
    Continuous f := by
  classical
  obtain ⟨n, b, hb⟩ := Module.Finite.exists_fin (R := A) (M := B)
  let l : (Fin n → A) →ₗ[A] B := Fintype.linearCombination A b
  have hl : Function.Surjective l :=
    (span_range_eq_top_iff_surjective_fintypeLinearCombination A b).mp hb
  have hlc : Continuous l := by
    change Continuous (fun c : Fin n → A => ∑ i, c i • b i)
    simp_rw [Algebra.smul_def]
    exact continuous_finsetSum _ fun i _ =>
      (hAB.comp (continuous_apply i)).mul continuous_const
  let L : (Fin n → A) →L[K] B :=
    { l.restrictScalars K with cont := hlc }
  apply (L.isQuotientMap hl).continuous_iff.mpr
  change Continuous (fun c : Fin n → A => f (∑ i, c i • b i))
  simp_rw [map_sum, map_smul]
  simp_rw [Algebra.smul_def]
  exact continuous_finsetSum _ fun i _ =>
    (hAC.comp (continuous_apply i)).mul continuous_const

variable [NormedAlgebra K C] [IsScalarTower K A C]

/-- The continuity just proved gives a global linear norm bound, over
the original coefficient field. -/
theorem exists_norm_bound (f : B →ₐ[A] C)
    (hAB : Continuous (algebraMap A B)) (hAC : Continuous (algebraMap A C)) :
    ∃ M ≥ (0 : ℝ), ∀ b : B, ‖f b‖ ≤ M * ‖b‖ := by
  let L : B →L[K] C :=
    { (f.restrictScalars K).toLinearMap with
      cont := continuous_algHom (K := K) f hAB hAC }
  exact ⟨‖L‖, norm_nonneg L, fun b => L.le_opNorm b⟩

end Langlands.Analytic.FiniteBanachAlgebra

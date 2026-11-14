import Langlands.Representation.Induction.CompactScalarProof
import Langlands.AllField.Group.GL.BlockModulusHaarProof
import Langlands.AllField.Representation.Induction.CompactScalarStatement
/-!
# Proof of the scalar compact-picture integral for standard GL parabolics

The compact open subgroup is the level-zero subgroup `GL_n(O_F)`, the factorization
`G = P K` is the Iwasawa decomposition, and the Haar probability measure on `K` is the
restriction of the mass-one Haar measure `generalLinearHaar` of `GL_n(F)`. The full Levi
modulus of the block parabolic is Mathlib's modular character of the parabolic, so the
invariance is the abstract compact averaging theorem.
-/

noncomputable section

namespace Langlands.AllField

open _root_.MeasureTheory Measure
open Langlands.GeneralLinear
open scoped NNReal

universe uF

/-- **The scalar compact-picture integral.** For every standard block parabolic `P` of
`GL_n(F)` with `n > 0`, the Haar probability measure on `K = GL_n(O_F)` integrates every
locally constant function covariant on the left by the full modulus of `P` to a value
invariant under all right translations. -/
theorem glParabolicCompactScalarIntegral : GLParabolicCompactScalarIntegralStatement.{uF} := by
  intro F _ T n hn B
  obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have := T.fieldT2
  have := T.generalLinearTopologicalGroup (n + 1)
  have := T.generalLinearLocallyCompactSpace (n + 1)
  have := T.generalLinearSecondCountableTopology (n + 1)
  have := T.parabolicLocallyCompactSpace B
  let K := Conductor.levelOpenSubgroup F n 0
  have hKc : IsCompact (K : Set (GeneralLinear (n + 1) F)) :=
    Conductor.isCompact_levelOpenSubgroup F n 0
  have hPK : ∀ g : GeneralLinear (n + 1) F, ∃ q ∈ B.parabolic F,
      ∃ k ∈ (K : Subgroup (GeneralLinear (n + 1) F)), g = q * k := by
    intro g
    obtain ⟨k, hk, hup⟩ :=
      Iwasawa.exists_mul_upperTriangular (ValuativeRel.valuation F) (n + 1) g
    have hkK : k ∈ (K : Subgroup (GeneralLinear (n + 1) F)) := by
      change k ∈ Conductor.levelSubgroup F n 0
      rw [Conductor.levelSubgroup_zero, ← Iwasawa.integralRange_succ]
      exact hk
    exact ⟨g * k, B.mem_parabolic_of_isUpperTriangular _ hup, k⁻¹, inv_mem hkK,
      (mul_inv_cancel_right g k).symm⟩
  refine ⟨K, hKc, fun g => ?_, ?_⟩
  · obtain ⟨q, hq, k, hk, h⟩ := hPK g
    exact ⟨⟨q, hq⟩, ⟨k, hk⟩, h⟩
  let _ : MeasurableSpace (GeneralLinear (n + 1) F) := borel _
  have : BorelSpace (GeneralLinear (n + 1) F) := ⟨rfl⟩
  have hKm : MeasurableSet (K : Set (GeneralLinear (n + 1) F)) :=
    K.isOpen.measurableSet
  let μ : Measure (GeneralLinear (n + 1) F) :=
    RankinSelberg.generalLinearHaar F n
  have hμK : μ (K : Set (GeneralLinear (n + 1) F)) = 1 := by
    have h := RankinSelberg.generalLinearHaar_integralSubgroup F n
    rw [← Conductor.levelSubgroup_zero] at h
    exact h
  -- The Borel structure of `K` is the subspace structure of the Borel structure of `G`.
  have hborel : (borel K : MeasurableSpace K) = Subtype.instMeasurableSpace :=
    (Subtype.borelSpace (· ∈ K)).measurable_eq.symm
  rw [hborel]
  let κ : Measure K := μ.comap Subtype.val
  have hκ : IsHaarMeasure κ :=
    IsHaarMeasure.comap (mH := inferInstance) μ
      (f := (K : Subgroup (GeneralLinear (n + 1) F)).subtype)
      K.isOpen.isOpenEmbedding_subtypeVal
  have hκ1 : κ Set.univ = 1 := by
    have h := comap_subtype_coe_apply hKm μ
      (Set.univ : Set (K : Set (GeneralLinear (n + 1) F)))
    rw [Set.image_univ, Subtype.range_coe] at h
    exact h.trans hμK
  have : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  refine ⟨κ, hκ, ⟨hκ1⟩, fun φ hφ hcov g => ⟨?_, ?_⟩⟩
  · exact (hφ.continuous.comp (continuous_subtype_val.mul continuous_const))
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · have hcov' (q : B.parabolic F) (x : GeneralLinear (n + 1) F) :
        φ ((q : GeneralLinear (n + 1) F) * x) =
          (((modularCharacter q : ℝ≥0) : ℝ) : ℂ) * φ x := by
      rw [B.modularCharacter_eq (T.leviModulus B) (glBlockModulusHaar F T (n + 1) B) q]
      exact hcov q x
    have h := ModularCompactAverage.setIntegral_mul_right_eq μ (B.parabolic F)
      (B.isClosed_parabolic F) (K : Subgroup (GeneralLinear (n + 1) F))
      K.isOpen hKc hPK φ hφ.continuous hcov' g
    have h1 := integral_subtype_comap (μ := μ) hKm (fun x => φ (x * g))
    have h2 := integral_subtype_comap (μ := μ) hKm φ
    exact h1.trans (h.trans h2.symm)

end Langlands.AllField

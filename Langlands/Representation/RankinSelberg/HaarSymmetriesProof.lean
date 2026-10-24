import Langlands.Representation.RankinSelberg.HaarSymmetriesStatement
import Langlands.Representation.RankinSelberg.GeneralLinearUnimodularity

/-!
# Proof of the symmetries of normalized GL Haar measure
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory
open scoped Pointwise ENNReal

universe uG uF

private theorem normalizedHaar_eq
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ ν : Measure G) [μ.IsHaarMeasure] [μ.Regular] [ν.IsMulLeftInvariant]
    [ν.Regular]
    (K : Set G) (hμ : μ K = 1) (hν : ν K = 1) : ν = μ := by
  have he := Measure.isMulLeftInvariant_eq_smul_of_regular ν μ
  have hc : Measure.haarScalarFactor ν μ = 1 := by
    apply ENNReal.coe_injective
    have hv := congrArg (fun m : Measure G => m K) he
    simpa only [hν, Measure.smul_apply, hμ, ENNReal.smul_def, smul_eq_mul,
      mul_one, ENNReal.coe_one] using hv.symm
  rw [he, hc, one_smul]

private theorem normalizedCompactOpenHaar_inv
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    [Measure.IsMulRightInvariant (normalizedCompactOpenHaar K hK)] :
    Measure.IsInvInvariant (normalizedCompactOpenHaar K hK) := by
  constructor
  apply normalizedHaar_eq _ _ (K : Set G) (normalizedCompactOpenHaar_self K hK)
  rw [Measure.inv_apply]
  simpa only [inv_coe_set] using normalizedCompactOpenHaar_self K hK

private theorem inverseTranspose_mem_integral
    (F : Type uF) [Field F] (n : ℕ) (O : Subring F)
    (g : Matrix.GeneralLinearGroup (Fin (n + 1)) F) :
    GeneralLinear.inverseTranspose (n + 1) F g ∈ Conductor.integralSubgroup O n ↔
      g ∈ Conductor.integralSubgroup O n := by
  simp only [Conductor.mem_integralSubgroup, ← map_inv,
    GeneralLinear.inverseTranspose_entry, inv_inv]
  constructor
  · rintro ⟨hi, hg⟩
    exact ⟨fun i j => hg j i, fun i j => hi j i⟩
  · rintro ⟨hg, hi⟩
    exact ⟨fun i j => hi j i, fun i j => hg j i⟩

/-- All four symmetries preserve the existing integral-subgroup-normalized measure. -/
theorem generalLinearHaarSymmetries
    (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℕ)
    [MeasurableSpace (Matrix.GeneralLinearGroup (Fin (n + 1)) F)]
    [BorelSpace (Matrix.GeneralLinearGroup (Fin (n + 1)) F)] :
    GeneralLinearHaarSymmetriesStatement F n := by
  have : T2Space F := by
    let := IsTopologicalAddGroup.rightUniformSpace F
    have := isUniformAddGroup_of_addCommGroup (G := F)
    infer_instance
  have : LocallyCompactSpace (Matrix (Fin (n + 1)) (Fin (n + 1)) F) :=
    inferInstanceAs (LocallyCompactSpace (Fin (n + 1) → Fin (n + 1) → F))
  let G := Matrix.GeneralLinearGroup (Fin (n + 1)) F
  let μ := generalLinearHaar F n
  have : Measure.IsMulRightInvariant
      (normalizedCompactOpenHaar (Conductor.levelOpenSubgroup F n 0)
        (Conductor.isCompact_levelOpenSubgroup F n 0)) :=
    generalLinearHaar_isMulRightInvariant F n
  have hinv : Measure.IsInvInvariant μ :=
    normalizedCompactOpenHaar_inv (Conductor.levelOpenSubgroup F n 0)
      (Conductor.isCompact_levelOpenSubgroup F n 0)
  let e := GeneralLinear.inverseTransposeContinuous (n + 1) F
  have hemeas : Measurable (e : G → G) := e.continuous.measurable
  have he : MeasurePreserving e μ μ := by
    refine ⟨hemeas, ?_⟩
    have : (Measure.map e μ).Regular :=
      Measure.Regular.map (μ := μ) e.toHomeomorph
    let K := Conductor.integralSubgroup (ValuativeRel.valuation F).integer n
    have hK : MeasurableSet (K : Set G) :=
      (Conductor.isOpen_integralSubgroup _ _
        (Valuation.isOpen_integer (v := ValuativeRel.valuation F))).measurableSet
    apply normalizedHaar_eq μ (Measure.map e μ) (K : Set G)
      (generalLinearHaar_integralSubgroup F n)
    rw [Measure.map_apply hemeas hK]
    have hpre : e ⁻¹' (K : Set G) = (K : Set G) := by
      ext g
      exact inverseTranspose_mem_integral F n _ g
    rw [hpre]
    exact generalLinearHaar_integralSubgroup F n
  refine ⟨hinv, he, ?_, ?_⟩
  · exact he.comp (Measure.measurePreserving_inv μ)
  · intro a
    exact (measurePreserving_mul_right μ a⁻¹).comp (measurePreserving_mul_left μ a)

-- Inspect the full outer parameter telescope without elaborating an application.
example : ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℕ)
    [MeasurableSpace (Matrix.GeneralLinearGroup (Fin (n + 1)) F)]
    [BorelSpace (Matrix.GeneralLinearGroup (Fin (n + 1)) F)],
    GeneralLinearHaarSymmetriesStatement F n :=
  @generalLinearHaarSymmetries

end Langlands.RankinSelberg

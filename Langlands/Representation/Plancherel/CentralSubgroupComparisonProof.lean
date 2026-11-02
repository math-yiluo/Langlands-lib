import Langlands.Representation.Plancherel.CentralSubgroupComparisonStatement
import Langlands.Representation.MatrixCoefficient.NormRegularityProof
import Langlands.Analysis.CompactKernelHaarLpProof

/-! # Actual central-quotient topology and coefficient comparison -/

namespace Langlands.Plancherel

open MeasureTheory

universe uG uV

/-- The actual central projection is open, surjective, has compact kernel,
and is proper when the center modulo the given subgroup is compact. -/
theorem centralQuotientCompactKernel : CentralQuotientCompactKernelStatement.{uG} := by
  intro G _ _ _ _ _ A _ hA hclosed _
  have : IsClosed (A : Set G) := hclosed
  have : IsClosed (Subgroup.center G : Set G) := by
    simpa only [Set.centralizer_univ, Subgroup.coe_center] using
      (Set.isClosed_centralizer (Set.univ : Set G))
  have hsurj : Function.Surjective (centralQuotientProjection A hA) := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨QuotientGroup.mk g, rfl⟩
  have hopen : IsOpenMap (centralQuotientProjection A hA) := by
    apply (QuotientGroup.isOpenQuotientMap_mk (N := A)).isOpenMap_iff.mpr
    exact QuotientGroup.isOpenMap_coe
  let f : (Subgroup.center G ⧸ A.subgroupOf (Subgroup.center G)) →* (G ⧸ A) :=
    QuotientGroup.map (A.subgroupOf (Subgroup.center G)) A
      (Subgroup.center G).subtype (by intro z hz; exact hz)
  have hf : Continuous f := by
    apply (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
    exact QuotientGroup.continuous_mk.comp continuous_subtype_val
  have hrange : Set.range f = ((centralQuotientProjection A hA).ker : Set (G ⧸ A)) := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      induction z using Quotient.inductionOn with
      | h z =>
        change (QuotientGroup.mk (z : G) : G ⧸ Subgroup.center G) = 1
        exact (QuotientGroup.eq_one_iff _).mpr z.property
    · intro hx
      induction x using Quotient.inductionOn with
      | h g =>
        have hg : g ∈ Subgroup.center G :=
          (QuotientGroup.eq_one_iff g).mp hx
        exact ⟨QuotientGroup.mk (⟨g, hg⟩ : Subgroup.center G), rfl⟩
  have hker : IsCompact ((centralQuotientProjection A hA).ker : Set (G ⧸ A)) := by
    rw [← hrange]
    exact isCompact_range hf
  exact ⟨hsurj, hopen, hker,
    compactKernelProperMap (G ⧸ A) (G ⧸ Subgroup.center G)
      (centralQuotientProjection A hA) hsurj hopen hker⟩

/-- The actual coefficient Lp conditions and square-integrability predicates
agree on the two actual quotients, for independently chosen Haar measures. -/
theorem centralSubgroupCoefficientLpComparison :
    CentralSubgroupCoefficientLpComparisonStatement.{uG, uV} := by
  intro G _ _ _ _ _ _ A _ hA hclosed _ _ _ _ _ μA μZ _ _ V _ _ ρ
  have : IsClosed (A : Set G) := hclosed
  have : IsClosed (Subgroup.center G : Set G) := by
    simpa only [Set.centralizer_univ, Subgroup.coe_center] using
      (Set.isClosed_centralizer (Set.univ : Set G))
  obtain ⟨hsurj, hopen, hker, _⟩ := centralQuotientCompactKernel G A hA hclosed
  have hLp (c : UnitaryCentralCharacter ρ) (ℓ : Module.Dual ℂ V)
      (v : V) (p : ENNReal) (hv : IsSmoothVector ρ v) :
      MemLp (centralSubgroupCoefficientNorm A hA c ℓ v) p μA ↔
        MemLp (c.coefficientNorm ℓ v) p μZ :=
    (compactKernelHaarLpMeasure (G ⧸ A) (G ⧸ Subgroup.center G)
      (centralQuotientProjection A hA) hsurj hopen hker μA μZ).2.2
        ℝ (c.coefficientNorm ℓ v) p (c.continuous_coefficientNorm ℓ v hv)
  refine ⟨hLp, ?_⟩
  constructor
  · rintro ⟨hadm, c, hc⟩
    refine ⟨hadm, c, ?_⟩
    intro ℓ v
    exact (hLp c ℓ v 2 (hadm.1 v)).mp (hc ℓ v)
  · rintro ⟨hadm, c, hc⟩
    refine ⟨hadm, c, ?_⟩
    intro ℓ v
    exact (hLp c ℓ v 2 (hadm.1 v)).mpr (hc ℓ v)

/-- Topology and square-integrability comparison for an actual central subgroup. -/
theorem centralSubgroupSquareIntegrabilityComparison :
    CentralSubgroupSquareIntegrabilityComparisonStatement.{uG, uV} :=
  ⟨centralQuotientCompactKernel, centralSubgroupCoefficientLpComparison⟩

end Langlands.Plancherel

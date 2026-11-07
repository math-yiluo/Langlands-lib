import Langlands.Automorphic.GroupSchemeQuotientL2FiniteApproximationStatement
import Langlands.Global.FiniteAdelicGroupCompactOpenBasisProof
import Mathlib.Order.Filter.CountablyGenerated

/-! # Strong convergence of the original finite subgroup averages -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Filter
open scoped CategoryTheory.MonObj Topology

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme Langlands.Analysis

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
  (hi : Function.Injective (characterRestrict i))
  [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I]
  (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
  [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant]

local notation "μQ" => positiveRationalQuotientHaarMeasure F G T i
local notation "ρf" => haarQuotientL2FiniteRightAction F G T i hi I e hc

/-- A small original orbit on a subgroup gives a small difference of its actual average. -/
theorem norm_haarQuotientL2FiniteAverage_sub_le
    (K : OpenSubgroup (FiniteAdelicGroupPoints F G)) [CompactSpace K]
    (φ : Lp ℂ 2 μQ) (ε : ℝ)
    (hε : ∀ k : K, ‖ρf k φ - φ‖ ≤ ε) :
    ‖haarQuotientL2FiniteAverage F G T i hi I e hc K φ - φ‖ ≤ ε := by
  let : IsTopologicalGroup K := inferInstanceAs (IsTopologicalGroup K.toSubgroup)
  let : MeasurableSpace K := borel K
  let : BorelSpace K := ⟨rfl⟩
  calc
    ‖haarQuotientL2FiniteAverage F G T i hi I e hc K φ - φ‖ =
        ‖∫ k : K, ρf k φ - φ ∂compactProbabilityHaar K‖ := by
      simp only [haarQuotientL2FiniteRightAction_apply]
      rw [integral_sub
        (haarQuotientL2FiniteAverage_integrable F G T i hi I e hc K φ)
        (integrable_const φ), integral_const, probReal_univ, one_smul,
        haarQuotientL2FiniteAverage_apply]
    _ ≤ ε := by
      have hb : ‖∫ k : K, ρf k φ - φ ∂compactProbabilityHaar K‖ ≤
          ε * (compactProbabilityHaar K).real Set.univ :=
        norm_integral_le_of_norm_le_const (Eventually.of_forall hε)
      simpa only [probReal_univ, mul_one] using
        hb

/-- Exact original-space finite approximation and density target. -/
theorem groupSchemeQuotientL2FiniteApproximation :
    GroupSchemeQuotientL2FiniteApproximationStatement.{u} := by
  intro F _ _ G _ _ T i hi _ I _ e hc _
  obtain ⟨K, hK, hb⟩ :=
    ((finiteAdelicGroupCompactOpenBasis F G).2).exists_antitone_subbasis
  let A := fun n =>
    let : CompactSpace (K n) := isCompact_iff_compactSpace.mp (hK n)
    haarQuotientL2FiniteAverage F G T i hi I e hc (K n)
  have hfixed : ∀ n (φ : Lp ℂ 2 (positiveRationalQuotientHaarMeasure F G T i)),
      A n φ ∈ Langlands.fixedVectors
        (haarQuotientL2FiniteRightAction F G T i hi I e hc) (K n).toSubgroup := by
    intro n φ
    let : CompactSpace (K n) := isCompact_iff_compactSpace.mp (hK n)
    exact haarQuotientL2FiniteAverage_mem_fixedVectors F G T i hi I e hc (K n) φ
  have hconv : ∀ φ : Lp ℂ 2 (positiveRationalQuotientHaarMeasure F G T i),
      Tendsto (fun n => A n φ) atTop (𝓝 φ) := by
    intro φ
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    have hcont : Continuous (fun a : FiniteAdelicGroupPoints F G =>
        haarQuotientL2FiniteRightAction F G T i hi I e hc a φ) :=
      (haarQuotientL2OrbitMap F G T i hi I e hc φ).continuous.comp
        (AdelicGroupPoints.ofFinite F G).continuous
    have hsmall : {a : FiniteAdelicGroupPoints F G |
        ‖haarQuotientL2FiniteRightAction F G T i hi I e hc a φ - φ‖ < ε / 2} ∈
          𝓝 (1 : FiniteAdelicGroupPoints F G) := by
      change ∀ᶠ a in 𝓝 (1 : FiniteAdelicGroupPoints F G),
        ‖haarQuotientL2FiniteRightAction F G T i hi I e hc a φ - φ‖ < ε / 2
      simpa only [map_one, Module.End.one_apply, dist_eq_norm] using
        (Metric.continuousAt_iff'.mp (hcont.continuousAt (x := 1)) (ε / 2) (half_pos hε))
    obtain ⟨N, hN⟩ := hb.mem_iff.mp hsmall
    refine ⟨N, fun n hn => ?_⟩
    let : CompactSpace (K n) := isCompact_iff_compactSpace.mp (hK n)
    rw [dist_eq_norm]
    exact (norm_haarQuotientL2FiniteAverage_sub_le F G T i hi I e hc (K n) φ (ε / 2)
      (fun k => (hN (hb.antitone hn k.property)).le)).trans_lt (half_lt_self hε)
  refine ⟨K, hK, hb, hfixed, hconv, ?_⟩
  intro φ
  exact mem_closure_of_tendsto (hconv φ)
    (Eventually.of_forall (fun n => ⟨K n, hfixed n φ⟩))

end Langlands.Automorphic.GroupSchemeFunctions

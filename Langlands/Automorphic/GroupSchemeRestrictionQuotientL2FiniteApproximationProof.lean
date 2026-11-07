import Langlands.Automorphic.GroupSchemeRestrictionQuotientL2FiniteApproximationStatement
import Langlands.Global.FiniteAdelicGroupCompactOpenBasisProof
import Mathlib.Order.Filter.CountablyGenerated

/-! # Finite-level approximation in `L²([G])`: proof -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Filter
open scoped CategoryTheory.MonObj Topology

namespace Langlands.Global.RestrictionSplitCentre

open Langlands.GroupScheme PositiveRealTorus Langlands.Automorphic.GroupSchemeFunctions
open Langlands.Analysis

variable (F : Type) [Field F] [NumberField F]
variable (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
variable {S : CommGroupScheme (Spec (CommRingCat.of ℚ))}
variable {j : S.toGrp ⟶ AffineWeil.groupScheme ℚ F G}
variable {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G}
variable (h : subgroup F G S j = imageSubgroup F T G i)
variable (hi : Function.Injective (characterRestrict i))
variable [(characterRestrict i).range.FiniteIndex]
variable [(Measure.haar : Measure (AdelicGroupPoints.normOneSubgroup F G)).IsMulRightInvariant]
variable (hc : IsCentral i) (hT : IsSplitTorus T.toGrp)
variable (hInv' : QuotientRightInvariant F G (quotientHaarMeasure F G S j))

local notation "μ" => quotientHaarMeasure F G S j
local notation "ρf" =>
  rationalQuotientL2FiniteRightAction F G (quotientHaarMeasure F G S j) hInv'

attribute [local instance] finiteAverageTopologicalGroup finiteAverageSecondCountable
  finiteAverageMeasurableSpace finiteAverageBorelSpace

/-- If every translate of `φ` by the compact open subgroup `K` lies within `ε` of `φ`, then so
does the `K`-average of `φ`. -/
theorem norm_rationalQuotientL2FiniteAverage_sub_le
    (K : OpenSubgroup (FiniteAdelicGroupPoints F G)) [CompactSpace K]
    (φ : Lp ℂ 2 μ) (ε : ℝ) (hε : ∀ k : K, ‖ρf k φ - φ‖ ≤ ε) :
    ‖rationalQuotientL2FiniteAverage F G h hi hc hT hInv' K φ - φ‖ ≤ ε := by
  calc
    ‖rationalQuotientL2FiniteAverage F G h hi hc hT hInv' K φ - φ‖ =
        ‖∫ k : K, ρf k φ - φ ∂compactProbabilityHaar K‖ := by
      simp only [rationalQuotientL2FiniteRightAction_apply]
      rw [integral_sub
        (rationalQuotientL2FiniteAverage_integrable F G h hi hc hT hInv' K φ)
        (integrable_const φ), integral_const, probReal_univ, one_smul,
        rationalQuotientL2FiniteAverage_apply]
    _ ≤ ε := by
      have hb : ‖∫ k : K, ρf k φ - φ ∂compactProbabilityHaar K‖ ≤
          ε * (compactProbabilityHaar K).real Set.univ :=
        norm_integral_le_of_norm_le_const (Eventually.of_forall hε)
      simpa only [probReal_univ, mul_one] using hb

/-- Finite-level approximation and density of finite smooth vectors in `L²([G])`. -/
theorem quotientL2FiniteApproximation : QuotientL2FiniteApproximationStatement := by
  intro F _ _ G _ _ S j T i h hi _ hc hT _ hInv'
  obtain ⟨K, hK, hb⟩ :=
    ((finiteAdelicGroupCompactOpenBasis F G).2).exists_antitone_subbasis
  let A := fun n =>
    let : CompactSpace (K n) := isCompact_iff_compactSpace.mp (hK n)
    rationalQuotientL2FiniteAverage F G h hi hc hT hInv' (K n)
  have hfixed : ∀ n (φ : Lp ℂ 2 (quotientHaarMeasure F G S j)),
      A n φ ∈ Langlands.fixedVectors
        (rationalQuotientL2FiniteRightAction F G (quotientHaarMeasure F G S j) hInv')
        (K n).toSubgroup := by
    intro n φ
    let : CompactSpace (K n) := isCompact_iff_compactSpace.mp (hK n)
    exact rationalQuotientL2FiniteAverage_mem_fixedVectors F G h hi hc hT hInv' (K n) φ
  have hconv : ∀ φ : Lp ℂ 2 (quotientHaarMeasure F G S j),
      Tendsto (fun n => A n φ) atTop (𝓝 φ) := by
    intro φ
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    have hcont : Continuous (fun a : FiniteAdelicGroupPoints F G =>
        rationalQuotientL2FiniteRightAction F G (quotientHaarMeasure F G S j) hInv' a φ) :=
      (rationalQuotientL2OrbitMap F G hInv' h hi hc hT φ).continuous.comp
        (AdelicGroupPoints.ofFinite F G).continuous
    have hsmall : {a : FiniteAdelicGroupPoints F G |
        ‖rationalQuotientL2FiniteRightAction F G (quotientHaarMeasure F G S j) hInv' a φ - φ‖ <
          ε / 2} ∈ 𝓝 (1 : FiniteAdelicGroupPoints F G) := by
      change ∀ᶠ a in 𝓝 (1 : FiniteAdelicGroupPoints F G),
        ‖rationalQuotientL2FiniteRightAction F G (quotientHaarMeasure F G S j) hInv' a φ - φ‖ <
          ε / 2
      simpa only [map_one, Module.End.one_apply, dist_eq_norm] using
        (Metric.continuousAt_iff'.mp (hcont.continuousAt (x := 1)) (ε / 2) (half_pos hε))
    obtain ⟨N, hN⟩ := hb.mem_iff.mp hsmall
    refine ⟨N, fun n hn => ?_⟩
    let : CompactSpace (K n) := isCompact_iff_compactSpace.mp (hK n)
    rw [dist_eq_norm]
    exact (norm_rationalQuotientL2FiniteAverage_sub_le F G h hi hc hT hInv' (K n) φ (ε / 2)
      (fun k => (hN (hb.antitone hn k.property)).le)).trans_lt (half_lt_self hε)
  refine ⟨K, hK, hb, hfixed, hconv, ?_⟩
  intro φ
  exact mem_closure_of_tendsto (hconv φ)
    (Eventually.of_forall (fun n => ⟨K n, hfixed n φ⟩))

end Langlands.Global.RestrictionSplitCentre

import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOppositeModulusLevelDataStatement
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOppositeWeightContractionStatement
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.UnipotentIntersectionProduct
import Langlands.Representation.CuspidalSupport.RationalNormKernelPositiveGenerators
import Langlands.Representation.Plancherel.ParabolicCharacterDecayProof

/-! # Entry into a neighborhood of the identity at a prescribed modulus level -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Filter Topology
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.MatrixRepresentation
open Langlands.GroupScheme.SplitTorusValuation
open Langlands.BruhatTits.DynamicUnipotentContainment
open Langlands.Aubert.General.RationalPointFamily
  (oppositeUnipotent isClosed_oppositeUnipotent_localField)

namespace Langlands.HarishChandraSchwartz

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {i : S.toGrp ⟶ G} {ν ζ : cocharacterLattice S} {K : Subgroup (rationalPoints G)}
  {hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K}
  {L : oppositeUnipotent i ζ → ℤ} {W : Set (rationalPoints G)}

private theorem oppositeLevel_chartEntry_of_heightComparison
    (hcontraction : RationalOppositeWeightContractionStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hKc : IsCompact (K : Set (rationalPoints G)))
    {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N)) (hρ : IsClosedSubgroup ρ)
    (hw : ∀ x : oppositeUnipotent i ζ,
      iwasawaWeight hPK (rationalMinimalModulus i ν) (x : rationalPoints G) =
        (LocalField.residueCardinality F : ℝ) ^ (-(L x : ℝ) / 2))
    (hheight : LevelHeightComparison (oppositeUnipotent i ζ) L
      (LocalField.residueCardinality F : ℝ) (rationalHeight (F := F) ρ))
    (hW : W ∈ 𝓝 (1 : rationalPoints G)) :
    let a : rationalPoints G :=
      gmRationalPoint (uniformizerUnit F) ≫ (CommGroupScheme.groupHom ζ ≫ i).hom.hom
    ∃ j : ℕ, ∀ (n : ℕ) (x : oppositeUnipotent i ζ), L x = (n : ℤ) →
      (a ^ (n + j))⁻¹ * (x : rationalPoints G) * a ^ (n + j) ∈ W := by
  let U := oppositeUnipotent i ζ
  let χ := CommGroupScheme.groupHom ζ ≫ i
  let χopp := Dynamic.inverseCocharacter χ
  let t := uniformizerUnit F
  let a : rationalPoints G := gmRationalPoint t ≫ χ.hom.hom
  let q : ℝ := LocalField.residueCardinality F
  let w : rationalPoints G → ℝ := iwasawaWeight hPK (rationalMinimalModulus i ν)
  have hq : 1 < q := by
    change (1 : ℝ) < LocalField.residueCardinality F
    exact_mod_cast LocalField.residueCardinality_gt_one F
  have hq₀ : 0 < q := zero_lt_one.trans hq
  have ht : LocalField.residueNormalizedAbsoluteValue F (t : F) = q⁻¹ :=
    LocalField.residueNormalizedAbsoluteValue_of_ord_one F (LocalField.ord_uniformizer F)
  have htlt : LocalField.residueNormalizedAbsoluteValue F (t : F) < 1 :=
    ht ▸ inv_lt_one_of_one_lt₀ hq
  obtain ⟨C, _, hC⟩ := hcontraction F G hG S i hi ν hν ζ K hPK hKc t
    htlt
  have hdecay (n : ℕ) : (Real.sqrt (LocalField.residueNormalizedAbsoluteValue F (t : F))) ^ n =
      q ^ (-(n : ℝ) / 2) := by
    rw [ht, Real.sqrt_eq_rpow, Real.inv_rpow hq₀.le, ← Real.rpow_neg hq₀.le,
      ← Real.rpow_natCast, ← Real.rpow_mul hq₀.le]
    congr 1
    ring
  have haopp : cocharPoint χopp t = a⁻¹ := by
    rw [cocharPoint_inverseCocharacter, cocharPoint_eq_gmRationalPoint_comp]
  have haP : a⁻¹ ∈ (Dynamic.parabolic χopp).rationalPoints := by
    rw [← haopp]
    exact Dynamic.centralizer_le_parabolic χopp _ (cocharPoint_mem_centralizer χopp t)
  have hconj (n : ℕ) (x : U) : (a ^ n)⁻¹ * (x : rationalPoints G) * a ^ n ∈ U := by
    have hm := Dynamic.conj_mem_unipotent χopp
      ((Dynamic.parabolic χopp).rationalPoints.pow_mem haP n) x.property
    rw [inv_pow, inv_inv] at hm
    exact hm
  obtain ⟨C₀, C₁, _, hC₁, _, hheight⟩ := hheight
  let R := (C₀ + 2 * Real.log (2 * C) - C₁) / C₁
  let A : Set (rationalPoints G) :=
    {g | rationalHeight (F := F) ρ g ≤ R} ∩ (U : Set (rationalPoints G))
  have hA : IsCompact A := (isCompact_rationalHeight_le ρ hρ R).inter_right
    (isClosed_oppositeUnipotent_localField i ζ)
  have hmem (n : ℕ) (x : U) (hx : L x = (n : ℤ)) :
      (a ^ n)⁻¹ * (x : rationalPoints G) * a ^ n ∈ A := by
    let y : U := ⟨(a ^ n)⁻¹ * (x : rationalPoints G) * a ^ n, hconj n x⟩
    have hinv : (w (y : rationalPoints G))⁻¹ ≤ 2 * C := by
      have hy := hC n x
      change (w (y : rationalPoints G))⁻¹ ≤
        C * (1 + (Real.sqrt (LocalField.residueNormalizedAbsoluteValue F (t : F))) ^ n *
          (w (x : rationalPoints G))⁻¹) at hy
      have hwx : w (x : rationalPoints G) = q ^ (-(L x : ℝ) / 2) := hw x
      rw [hdecay, hwx, hx, Int.cast_natCast,
        mul_inv_cancel₀ (Real.rpow_pos_of_pos hq₀ _).ne'] at hy
      linarith
    have hwy : w (y : rationalPoints G) = q ^ (-(L y : ℝ) / 2) := hw y
    have hpos : 0 < w (y : rationalPoints G) := iwasawaWeight_pos _
    have hlog := Real.log_le_log (inv_pos.mpr hpos) hinv
    rw [Real.log_inv, hwy, Real.log_rpow hq₀] at hlog
    refine ⟨(le_div_iff₀ hC₁).2 ?_, y.property⟩
    linarith [(hheight y).1]
  obtain ⟨j, hj⟩ := (eventually_cocharPoint_pow_conj_mem_ambient χopp t
    (tendsto_uniformizerUnit_pow_zero F) A hA Set.inter_subset_right W hW).exists
  refine ⟨j, fun n x hx => ?_⟩
  have hxW := hj _ (hmem n x hx)
  simpa only [haopp, inv_pow, inv_inv, pow_add, mul_inv_rev, mul_assoc] using hxW

/-- One fixed number of additional powers brings every nonnegative modulus level into
any prescribed identity neighborhood after the level number of contraction powers. -/
theorem exists_oppositeLevel_chart_entry
    (hcontraction : RationalOppositeWeightContractionStatement.{u})
    (hlevels : RationalOppositeModulusLevelDataStatement.{u})
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) {J : Set (characterLattice S)}
    (hζ : IsStandardCocharacter i ν J ζ) (hKo : IsOpen (K : Set (rationalPoints G)))
    (hKc : IsCompact (K : Set (rationalPoints G)))
    (hw : ∀ x : oppositeUnipotent i ζ,
      iwasawaWeight hPK (rationalMinimalModulus i ν) (x : rationalPoints G) =
        (LocalField.residueCardinality F : ℝ) ^ (-(L x : ℝ) / 2))
    (hW : W ∈ 𝓝 (1 : rationalPoints G)) :
    let a : rationalPoints G :=
      gmRationalPoint (uniformizerUnit F) ≫ (CommGroupScheme.groupHom ζ ≫ i).hom.hom
    ∃ j : ℕ, ∀ (n : ℕ) (x : oppositeUnipotent i ζ), L x = (n : ℤ) →
      (a ^ (n + j))⁻¹ * (x : rationalPoints G) * a ^ (n + j) ∈ W := by
  let := hG.smooth
  let := hG.connectedSpace
  obtain ⟨N, ρ, hρ⟩ := Plancherel.exists_isClosedSubgroup_fin_succ G
  obtain ⟨L', _, hw', hheight⟩ := hlevels F G hG S i hi ν hν J ζ hζ K hKo hPK hKc
    (N + 1) ρ hρ
  have hq : (1 : ℝ) < LocalField.residueCardinality F := by
    exact_mod_cast LocalField.residueCardinality_gt_one F
  have hL : L = L' := by
    funext x
    have h := (Real.strictMono_rpow_of_base_gt_one hq).injective ((hw x).symm.trans (hw' x))
    have hcast : (L x : ℝ) = (L' x : ℝ) := by linarith
    exact_mod_cast hcast
  exact oppositeLevel_chartEntry_of_heightComparison hcontraction hG hi hν hKc ρ hρ hw
    (hL.symm ▸ hheight) hW

end Langlands.HarishChandraSchwartz

import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalMinimalLeviDominantReduction
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalConstantTermPolynomialBound
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalXiFullChamber

/-! # Extending the Xi upper estimate to the full minimal-Levi closed chamber -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal Pointwise
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)

include hG hi hν in
/-- Every uniformizer point of the maximal split torus is central in the actual minimal Levi. -/
theorem minimalLeviUniformizer_commute (y : cocharacterLattice S)
    (m : standardLeviPoints i ν ∅) :
    Commute (minimalLeviUniformizer (i := i) (ν := ν) y) m := by
  have hm : (m : rationalPoints G) ∈ (torusCentralizer i).carrier (Over.mk (𝟙 _)) := by
    rw [torusCentralizer_carrier_base, ← standardLeviPoints_empty_eq_centralizerPoints hG hi hν]
    exact m.2
  have hc := hm (Over.mk (𝟙 _)) (𝟙 _)
    (Langlands.Plancherel.RenardCartan.uniformizerSection S (.ofAdd y))
  apply Subtype.ext
  simpa only [Subgroup.coe_mul, coe_minimalLeviUniformizer,
    Langlands.Aubert.General.uniformizerPowers, MonoidHom.comp_apply,
    rationalPoints.map_apply, Category.id_comp] using hc.eq.symm

section Upper

variable [LocallyOfFiniteType G.X.hom]
  {K : Subgroup (rationalPoints G)} (hKo : IsOpen (K : Set (rationalPoints G)))
  (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K)

/-- The natural-degree upper Xi bound on all points of the actual minimal-Levi closed chamber. -/
def HasMinimalLeviXiUpperBound {n : ℕ} [Nonempty (Fin n)]
    (ρ : MatrixRepresentation G (Fin n)) : Prop :=
  ∃ C > 0, ∃ d : ℕ, ∀ m ∈ rationalMinimalClosedChamber hG hi hν,
    rationalXi hKc hPK (m : rationalPoints G) ≤
      C * minimalLeviSqrtModulus (i := i) (ν := ν) m *
        (1 + rationalHeight (F := F) ρ (m : rationalPoints G)) ^ d

include hKo in
/-- The separately owned lattice-section Xi upper statement implies its full-minimal-Levi
closed-chamber version, using only the supplied minimal-Levi Cartan covering for extension. -/
theorem hasMinimalLeviXiUpperBound_of_upperBound
    (hupper : RationalXiUpperBoundStatement.{u})
    {K0 : Subgroup (rationalPoints G)} (hK0 : IsCompact (K0 : Set (rationalPoints G)))
    (hbasis : SimultaneousStandardBasisAt i ν K0)
    (hcover : StandardLeviCartanCovering F i ν ∅ K0)
    {n : ℕ} [Nonempty (Fin n)] (ρ : MatrixRepresentation G (Fin n))
    (hρ : IsClosedSubgroup ρ) :
    HasMinimalLeviXiUpperBound hG hi hν hKc hPK ρ := by
  obtain ⟨Q, hQ, hreduce⟩ :=
    hasCompactDominantMinimalLeviReduction_of_cartanCovering hG hi hν hK0 hcover
  let C : Set (rationalPoints G) :=
    (fun m : standardLeviPoints i ν ∅ => (m : rationalPoints G)) '' (Q * Q)
  have hC : IsCompact C := (hQ.mul hQ).image continuous_subtype_val
  have hCP : C ⊆ (standardParabolicPoints i ν ∅ : Set (rationalPoints G)) := by
    rintro g ⟨m, _, rfl⟩
    exact standardLevi_le_standardParabolic i ν ∅ _ m.2
  have hA := isCompatibleStandardSplitComponent_minimal_id hG hi hν
  have hsection := hupper.xiUpperBound hG hi hν hbasis hA hKo hKc hPK hρ
  have hthick := xiUpperBound_iwasawa_compact_mul
    (fun p hp => rationalMinimalModulus_eq_one i ν hKo hKc p hp) hKo
    (rationalXi_nonneg hKc hPK) (rationalXi_uniformTranslationBound hKo hKc hPK)
    (fun k hk g => by simpa only [mul_one] using rationalXi_mul_mul hKo hKc hPK hk K.one_mem g)
    (rationalHeight_nonneg ρ) (continuous_rationalHeight ρ)
    (rationalHeight_mul_le ρ) (rationalHeight_inv ρ) hC hCP hsection
  obtain ⟨c, d, hbound⟩ := hthick
  refine ⟨max c 1, zero_lt_one.trans_le (le_max_right _ _), ⌈d⌉₊, fun m hm => ?_⟩
  obtain ⟨k₁, hk₁, k₂, hk₂, y, hy, hmeq⟩ := hreduce m hm
  have hcomm := (minimalLeviUniformizer_commute hG hi hν y k₂).eq
  have hm' : m = (k₁ * k₂) * minimalLeviUniformizer (i := i) (ν := ν) y := by
    rw [hmeq, mul_assoc, hcomm]
    group
  have hsectiony : Langlands.Aubert.General.uniformizerPowers i (.ofAdd y) ∈
      standardComponentCAplus i ν ∅ (𝟙 S.toGrp) :=
    (uniformizerPowers_mem_standardComponentChambers hi
      ⟨ν, isStandardCocharacter_empty_self i ν⟩ hA y (by simp) hy).2
  have hmem : (m : rationalPoints G) ∈ C * standardComponentCAplus i ν ∅ (𝟙 S.toGrp) := by
    refine Set.mem_mul.mpr ⟨(k₁ * k₂ : standardLeviPoints i ν ∅),
      ⟨k₁ * k₂, Set.mem_mul.mpr ⟨k₁, hk₁, k₂, hk₂, rfl⟩, rfl⟩,
      Langlands.Aubert.General.uniformizerPowers i (.ofAdd y), hsectiony, ?_⟩
    rw [← coe_minimalLeviUniformizer, ← Subgroup.coe_mul, ← hm']
  have hb := hbound (m : rationalPoints G) hmem
  have hw : iwasawaWeight hPK (rationalMinimalModulus i ν) (m : rationalPoints G) =
      minimalLeviSqrtModulus (i := i) (ν := ν) m := by
    unfold minimalLeviSqrtModulus
    simpa only [mul_one] using iwasawaWeight_mul (hPK := hPK)
      (fun p hp => rationalMinimalModulus_eq_one i ν hKo hKc p hp)
      (standardLevi_le_standardParabolic i ν ∅ _ m.2) K.one_mem
  rw [hw] at hb
  have hbase : 1 ≤ 1 + rationalHeight (F := F) ρ (m : rationalPoints G) :=
    le_add_of_nonneg_right (rationalHeight_nonneg ρ _)
  have hw0 : 0 ≤ minimalLeviSqrtModulus (i := i) (ν := ν) m := NNReal.coe_nonneg _
  calc rationalXi hKc hPK (m : rationalPoints G)
      ≤ c * minimalLeviSqrtModulus (i := i) (ν := ν) m *
        (1 + rationalHeight (F := F) ρ (m : rationalPoints G)) ^ d := hb
    _ ≤ max c 1 * minimalLeviSqrtModulus (i := i) (ν := ν) m *
        (1 + rationalHeight (F := F) ρ (m : rationalPoints G)) ^ d :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hw0)
        (Real.rpow_nonneg (zero_le_one.trans hbase) _)
    _ ≤ max c 1 * minimalLeviSqrtModulus (i := i) (ν := ν) m *
        (1 + rationalHeight (F := F) ρ (m : rationalPoints G)) ^ (⌈d⌉₊ : ℝ) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hbase (Nat.le_ceil d))
        (mul_nonneg (zero_le_one.trans (le_max_right _ _)) hw0)
    _ = _ := by rw [Real.rpow_natCast]

end Upper

end Langlands.HarishChandraSchwartz

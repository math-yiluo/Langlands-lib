import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalMinimalLeviXiUpper
import Langlands.BruhatTits.SpecialCompact.StandardLeviBasisInheritance

/-! # Full-minimal-Levi upper/lower Xi comparison for positive constant terms -/

noncomputable section

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal Pointwise
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

section CompactLower

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  {P K : Subgroup Γ} {hPK : IsIwasawaPair P K} {δ : P →* ℝ≥0ˣ}
  {Ξ : Γ → ℝ} {C T : Set Γ}

/-- A lower Iwasawa-weight estimate extends across a compact left thickening in the
parabolic, by compact uniformity of the reverse Xi translation and the half-weight. -/
theorem xiLowerBound_iwasawa_compact_mul
    (hδ : ∀ p : P, (p : Γ) ∈ K → δ p = 1)
    (hKo : IsOpen (K : Set Γ)) (hΞ : ∀ g, 0 ≤ Ξ g)
    (htrans : UniformTranslationBound Ξ) (hKΞ : ∀ k ∈ K, ∀ g, Ξ (k * g) = Ξ g)
    (hC : IsCompact C) (hCP : C ⊆ (P : Set Γ))
    (hlower : XiLowerBound Ξ T (iwasawaWeight hPK δ)) :
    XiLowerBound Ξ (C * T) (iwasawaWeight hPK δ) := by
  obtain ⟨c, hc⟩ := hlower
  obtain ⟨L, hL⟩ := htrans.exists_uniform_left hΞ hKo hKΞ hC.inv
  obtain ⟨B, hB⟩ := hC.bddAbove_image
    (continuous_iwasawaWeight (hPK := hPK) hδ hKo).continuousOn
  refine ⟨max B 0 * max c 0 * max L 0, ?_⟩
  rintro g ⟨k, hk, b, hb, rfl⟩
  have hwk : iwasawaWeight hPK δ k ≤ max B 0 :=
    (hB ⟨k, hk, rfl⟩).trans (le_max_left _ _)
  have hwb : iwasawaWeight hPK δ b ≤ max c 0 * Ξ b :=
    (hc b hb).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hΞ b))
  have hrev : Ξ b ≤ max L 0 * Ξ (k * b) := by
    have h := hL k⁻¹ (by simpa only [Set.mem_inv, inv_inv] using hk) (k * b)
    rw [inv_mul_cancel_left] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hΞ _))
  have hwkb : iwasawaWeight hPK δ (k * b) =
      iwasawaWeight hPK δ k * iwasawaWeight hPK δ b := by
    have hw := iwasawaWeight_mul (hPK := hPK) hδ (hCP hk) K.one_mem
    rw [mul_one] at hw
    rw [hw]
    exact iwasawaWeight_mul_left hδ ⟨k, hCP hk⟩ b
  rw [hwkb]
  calc iwasawaWeight hPK δ k * iwasawaWeight hPK δ b
      ≤ max B 0 * (max c 0 * Ξ b) :=
        mul_le_mul hwk hwb (iwasawaWeight_nonneg _) (le_max_right _ _)
    _ ≤ max B 0 * (max c 0 * (max L 0 * Ξ (k * b))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hrev (le_max_right _ _)) (le_max_right _ _)
    _ = _ := by ring

end CompactLower

section Actual

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

local instance : SecondCountableTopology (rationalPoints G) :=
  rationalPoint_secondCountableTopology F G

local instance (L : Subgroup (rationalPoints G)) : SecondCountableTopology L :=
  TopologicalSpace.Subtype.secondCountableTopology _

local instance lowerLeviAffine (J : Set (characterLattice S)) :
    IsAffineHom (Standard.leviScheme i ν J).X.hom := leviScheme_isAffineHom i ν J

local instance lowerLeviFiniteType (J : Set (characterLattice S)) :
    LocallyOfFiniteType (Standard.leviScheme i ν J).X.hom :=
  leviScheme_locallyOfFiniteType i ν J

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) {J : Set (characterLattice S)}
  (hJ : J ⊆ simpleRelativeRoots i ν)
  {K : Subgroup (rationalPoints G)} (hKo : IsOpen (K : Set (rationalPoints G)))
  (hKc : IsCompact (K : Set (rationalPoints G)))
  (hM : IsIwasawaPair ((standardParabolicPoints i ν ∅).subgroupOf (standardLeviPoints i ν J))
    (K.subgroupOf (standardLeviPoints i ν J)))

/-- The actual Levi minimal half modulus is controlled by its actual Xi on the entire
minimal-Levi closed chamber, with one positive constant. -/
def HasStandardLeviXiLowerBoundOnMinimal : Prop :=
  ∃ C > 0, ∀ m ∈ rationalMinimalClosedChamber hG hi hν,
    standardLeviSqrtModulusOnMinimal hG hi hν (J := J) m ≤
      C * rationalLeviXi hKc hM (minimalLeviInclusion hG hi hν J m)

omit [LocallyOfFiniteType G.X.hom] in
/-- The canonical intrinsic Levi point of a uniformizer cocharacter is the inclusion
of the original minimal-Levi uniformizer point. -/
theorem leviSchemePointsEquiv_uniformizerPowers (y : cocharacterLattice S) :
    leviSchemePointsEquiv i ν J
      (Langlands.Aubert.General.uniformizerPowers (Standard.leviTorusHom i ν J) (.ofAdd y)) =
    minimalLeviInclusion hG hi hν J (minimalLeviUniformizer (i := i) (ν := ν) y) := by
  apply Subtype.ext
  change rationalPoints.map (Standard.leviHom i ν J)
    (rationalPoints.map (Standard.leviTorusHom i ν J) _) = _
  rw [coe_minimalLeviInclusion, coe_minimalLeviUniformizer]
  change _ = rationalPoints.map i _
  simp only [rationalPoints.map_apply, Category.assoc]
  change _ ≫ (Standard.leviTorusHom i ν J ≫ Standard.leviHom i ν J).hom.hom = _
  rw [Standard.leviTorusHom_comp]

include hJ hKo hKc in
/-- The literal Levi Iwasawa half weight on an original minimal-Levi point is its
minimal-Levi half modulus. -/
theorem iwasawaWeight_standardLeviMinimalModulusOf_minimalLeviInclusion
    (m : standardLeviPoints i ν ∅) :
    iwasawaWeight hM (standardLeviMinimalModulusOf i ν J)
      (minimalLeviInclusion hG hi hν J m) =
    standardLeviSqrtModulusOnMinimal hG hi hν (J := J) m := by
  have hmP : minimalLeviInclusion hG hi hν J m ∈
      (standardParabolicPoints i ν ∅).subgroupOf (standardLeviPoints i ν J) := by
    change (m : rationalPoints G) ∈ standardParabolicPoints i ν ∅
    exact standardLevi_le_standardParabolic i ν ∅ _ m.2
  have he := iwasawaWeight_mul (hPK := hM)
    (fun p hp => standardLeviMinimalModulusOf_eq_one hKo hKc hG hi hν hJ p hp)
    hmP (K.subgroupOf (standardLeviPoints i ν J)).one_mem
  unfold standardLeviSqrtModulusOnMinimal
  simpa only [mul_one, standardLeviMinimalModulusOf_apply, coe_minimalLeviInclusion] using he

include hJ hKo in
/-- The inherited basis lets the intrinsic Levi lower Xi estimate be used uniformly
on every original dominant uniformizer cocharacter. -/
theorem exists_standardLeviXi_lower_uniformizer
    {K0 : Subgroup (rationalPoints G)}
    (hbasis : SimultaneousStandardBasisAt i ν K0) :
    ∃ C : ℝ, ∀ y : cocharacterLattice S,
      (∀ α ∈ simpleRelativeRoots i ν, 0 ≤ latticePairing S α y) →
      iwasawaWeight hM (standardLeviMinimalModulusOf i ν J)
        (minimalLeviInclusion hG hi hν J (minimalLeviUniformizer (i := i) (ν := ν) y)) ≤
      C * rationalLeviXi hKc hM
        (minimalLeviInclusion hG hi hν J (minimalLeviUniformizer (i := i) (ν := ν) y)) := by
  classical
  let iL := Standard.leviTorusHom i ν J
  let eL := leviSchemePointsEquiv i ν J
  let KL := leviSchemeCompact K i ν J
  have hiL := Standard.isMaximalSplitTorus_leviTorusHom i ν J hi
  have hKLc : IsCompact (KL : Set (rationalPoints (Standard.leviScheme i ν J))) :=
    isCompact_leviSchemeCompact hKc
  have hKLo : IsOpen (KL : Set (rationalPoints (Standard.leviScheme i ν J))) :=
    isOpen_leviSchemeCompact hKo
  have hLPK := isIwasawaPair_leviSchemeCompact hG hi hν hJ hM
  obtain ⟨BL, hBL, hBLR⟩ :=
    SimultaneousStandardBasisAt.leviScheme i ν J hG hi hν hJ hbasis
  obtain ⟨-, A0, q0, hA0, hmembers⟩ := hBLR ∅ (Set.empty_subset _)
  obtain ⟨H, hHBL, hHK⟩ := hBL.2.mem_iff.mp (hKLo.mem_nhds KL.one_mem)
  have hHo := (hBL.1 H hHBL).2.2.1
  obtain ⟨Cl, hCl⟩ := exists_sqrt_rationalMinimalModulus_le_rationalXi hKLo hKLc
    (fun x hx => hHK hx) (hmembers H hHBL) hHo hLPK
  refine ⟨Cl, fun y hy => ?_⟩
  let r := Langlands.Aubert.General.uniformizerPowers iL (.ofAdd y)
  have hyL : ∀ α ∈ simpleRelativeRoots iL ν, 0 ≤ latticePairing S α y := by
    rw [simpleRelativeRoots_leviTorusHom_eq hG hi hν hJ]
    exact fun α hα => hy α (hJ hα)
  have hrC := (uniformizerPowers_mem_standardComponentChambers hiL
    ⟨ν, isStandardCocharacter_empty_self iL ν⟩ hA0 y (by simp) hyL).2
  have hrP := mem_standardParabolicPoints_of_mem_standardComponentCAplus hA0 hrC
  have hre : eL r = minimalLeviInclusion hG hi hν J
      (minimalLeviUniformizer (i := i) (ν := ν) y) :=
    leviSchemePointsEquiv_uniformizerPowers hG hi hν y
  have hbP : eL r ∈ (standardParabolicPoints i ν ∅).subgroupOf
      (standardLeviPoints i ν J) :=
    (mem_standardParabolicPoints_leviTorusHom_iff hG hi hν hJ r).mp hrP
  have hmod : standardLeviMinimalModulusOf i ν J ⟨eL r, hbP⟩ =
      rationalMinimalModulus iL ν ⟨r, hrP⟩ := by
    rw [standardLeviMinimalModulusOf_apply]
    exact standardLeviMinimalModulus_leviHom hG hi hν hJ ⟨r, hrP⟩
  have hw := iwasawaWeight_mul (hPK := hM)
    (fun p hp => standardLeviMinimalModulusOf_eq_one hKo hKc hG hi hν hJ p hp)
    hbP (K.subgroupOf (standardLeviPoints i ν J)).one_mem
  rw [mul_one, hmod] at hw
  rw [← hre, hw]
  have hc := hCl r hrP hrC
  rw [rationalXi_leviScheme hG hi hν hJ hKo hKc hM r] at hc
  exact hc

include hJ hKo in
/-- The published lower Xi estimate on the intrinsic Levi scheme and the inherited original
standard basis yield the full-minimal-Levi lower estimate. No Xi upper statement is assumed. -/
theorem hasStandardLeviXiLowerBoundOnMinimal
    {K0 : Subgroup (rationalPoints G)} (hK0 : IsCompact (K0 : Set (rationalPoints G)))
    (hbasis : SimultaneousStandardBasisAt i ν K0)
    (hcover : StandardLeviCartanCovering F i ν ∅ K0) :
    HasStandardLeviXiLowerBoundOnMinimal hG hi hν hKc hM := by
  classical
  let inc := minimalLeviInclusion hG hi hν J
  let T : Set (standardLeviPoints i ν J) :=
    {b | ∃ y : cocharacterLattice S,
      (∀ α ∈ simpleRelativeRoots i ν, 0 ≤ latticePairing S α y) ∧
      b = inc (minimalLeviUniformizer (i := i) (ν := ν) y)}
  have hδM : ∀ p : (standardParabolicPoints i ν ∅).subgroupOf (standardLeviPoints i ν J),
      (p : standardLeviPoints i ν J) ∈ K.subgroupOf (standardLeviPoints i ν J) →
      standardLeviMinimalModulusOf i ν J p = 1 :=
    fun p hp => standardLeviMinimalModulusOf_eq_one hKo hKc hG hi hν hJ p hp
  obtain ⟨Cl, hCl⟩ := exists_standardLeviXi_lower_uniformizer hG hi hν hJ hKo hKc hM hbasis
  have hlow : XiLowerBound (rationalLeviXi hKc hM) T
      (iwasawaWeight hM (standardLeviMinimalModulusOf i ν J)) := by
    refine ⟨Cl, ?_⟩
    rintro b ⟨y, hy, rfl⟩
    exact hCl y hy
  obtain ⟨Q, hQ, hreduce⟩ :=
    hasCompactDominantMinimalLeviReduction_of_cartanCovering hG hi hν hK0 hcover
  let CQ : Set (standardLeviPoints i ν J) := inc '' (Q * Q)
  have hinc : Continuous inc := continuous_subtype_val.subtype_mk _
  have hCQ : IsCompact CQ := (hQ.mul hQ).image hinc
  have hCQP : CQ ⊆ ((standardParabolicPoints i ν ∅).subgroupOf
      (standardLeviPoints i ν J) : Set (standardLeviPoints i ν J)) := by
    rintro b ⟨m, _, rfl⟩
    exact standardLevi_le_standardParabolic i ν ∅ _ m.2
  have hKMo : IsOpen ((K.subgroupOf (standardLeviPoints i ν J)) :
      Set (standardLeviPoints i ν J)) := hKo.preimage continuous_subtype_val
  have := compactSpace_subgroupOf_standardLevi (i := i) (ν := ν) (J := J) hKc
  have htrans : UniformTranslationBound (rationalLeviXi hKc hM) :=
    xi_uniformTranslationBound hδM hKMo
  have hXi0 : ∀ b, 0 ≤ rationalLeviXi hKc hM b :=
    fun b => (rationalLeviXi_pos hKo hKc hG hi hν hJ hM b).le
  have hKXi : ∀ k ∈ K.subgroupOf (standardLeviPoints i ν J), ∀ b,
      rationalLeviXi hKc hM (k * b) = rationalLeviXi hKc hM b :=
    fun _ hk _ => xi_mul_left hk _
  obtain ⟨C, hC⟩ := xiLowerBound_iwasawa_compact_mul hδM hKMo hXi0 htrans hKXi
    hCQ hCQP hlow
  refine ⟨max C 1, zero_lt_one.trans_le (le_max_right _ _), fun m hm => ?_⟩
  obtain ⟨k₁, hk₁, k₂, hk₂, y, hy, hmeq⟩ := hreduce m hm
  have hcomm := (minimalLeviUniformizer_commute hG hi hν y k₂).eq
  have hm' : m = (k₁ * k₂) * minimalLeviUniformizer (i := i) (ν := ν) y := by
    rw [hmeq, mul_assoc, hcomm]
    group
  have hmT : inc m ∈ CQ * T :=
    Set.mem_mul.mpr ⟨inc (k₁ * k₂),
      ⟨k₁ * k₂, Set.mem_mul.mpr ⟨k₁, hk₁, k₂, hk₂, rfl⟩, rfl⟩,
      inc (minimalLeviUniformizer (i := i) (ν := ν) y), ⟨y, hy, rfl⟩,
      by rw [← map_mul, ← hm']⟩
  have hb := hC (inc m) hmT
  have hw := iwasawaWeight_standardLeviMinimalModulusOf_minimalLeviInclusion
    hG hi hν hJ hKo hKc hM m
  rw [hw] at hb
  exact hb.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hXi0 _))

include hJ hKo in
/-- The full comparison needed in the constant-term polynomial bound follows from the
original structural premises and the separately owned lattice upper statement alone. -/
theorem hasRationalXiLeviComparison_of_upperBound
    (hupper : RationalXiUpperBoundStatement.{u})
    {K0 : Subgroup (rationalPoints G)} (hK0 : IsCompact (K0 : Set (rationalPoints G)))
    (hbasis : SimultaneousStandardBasisAt i ν K0)
    (hcover : StandardLeviCartanCovering F i ν ∅ K0)
    (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K)
    {n : ℕ} [Nonempty (Fin n)] (ρ : MatrixRepresentation G (Fin n))
    (hρ : IsClosedSubgroup ρ) :
    HasRationalXiLeviComparison hG hi hν hKc hPK hM ρ :=
  hasRationalXiLeviComparison_of_modulusBounds hG hi hν hJ hKc hPK hM ρ
    (hasMinimalLeviXiUpperBound_of_upperBound hG hi hν hKo hKc hPK hupper hK0 hbasis hcover ρ hρ)
    (hasStandardLeviXiLowerBoundOnMinimal hG hi hν hJ hKo hKc hM hK0 hbasis hcover)

end Actual

end Langlands.HarishChandraSchwartz

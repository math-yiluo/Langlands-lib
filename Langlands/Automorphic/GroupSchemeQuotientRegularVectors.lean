import Langlands.Automorphic.GroupSchemeQuotientMassBound
import Langlands.Analysis.NormalizedAverageApproximation
import Langlands.Global.FiniteAdelicGroupCompactOpenBasisProof
import Langlands.Representation.Unitary.CompactIsometricAverage
import Langlands.Global.AdelicGroupProduct
import Langlands.Global.AdelicGroupPolish

/-! # Nonzero vectors with regular continuous representatives in closed invariant subspaces -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry MeasureTheory NumberField Set Topology Filter
open scoped CategoryTheory.MonObj CompactlySupported Pointwise

set_option autoImplicit false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme
open Langlands.Analysis.NormalizedAverage

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)

local notation "Q" => PositiveRationalQuotient F G T i
local notation "Γ" => positiveRationalSubgroup F G T i
local notation "μQ" => positiveRationalQuotientHaarMeasure F G T i

section Invariance

/-- Invariance of a function on the quotient under right translation by a subgroup of the
finite adelic points. -/
def IsFiniteInvariant (h : Q → ℂ) (L : Subgroup (FiniteAdelicGroupPoints F G)) : Prop :=
  ∀ l ∈ L, ∀ q, h (LeftCosetSpace.rightTranslate Γ (AdelicGroupPoints.ofFinite F G l) q) = h q

omit [LocallyOfFiniteType G.X.hom] in
theorem isFiniteInvariant_bot (h : Q → ℂ) : IsFiniteInvariant F G T i h ⊥ := by
  intro l hl q
  rw [Subgroup.mem_bot.mp hl, map_one, LeftCosetSpace.rightTranslate_one]

variable {Y : Type v} [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
  (ν : Measure Y) [IsFiniteMeasureOnCompacts ν]

omit [LocallyOfFiniteType G.X.hom] in
/-- A weighted orbit integral along parameters commuting with a translation `g` is invariant
under `g` when the integrated function is. -/
theorem weightedQuotientOrbitIntegral_rightTranslate_of_commute (b : C(Y, AdelicGroupPoints F G))
    (w : C(Y, ℂ)) (hw : HasCompactSupport w) (h : C(Q, ℂ)) (g : AdelicGroupPoints F G)
    (hcomm : ∀ y, g * b y = b y * g)
    (hg : ∀ q, h (LeftCosetSpace.rightTranslate Γ g q) = h q) (q : Q) :
    weightedQuotientOrbitIntegral F G T i ν b w hw h (LeftCosetSpace.rightTranslate Γ g q) =
      weightedQuotientOrbitIntegral F G T i ν b w hw h q := by
  obtain ⟨x, rfl⟩ := LeftCosetSpace.mk_surjective Γ q
  simp only [weightedQuotientOrbitIntegral_apply, LeftCosetSpace.rightTranslate_mk]
  congr 1
  funext y
  rw [mul_assoc, hcomm y, ← mul_assoc, ← LeftCosetSpace.rightTranslate_mk, hg]

omit [LocallyOfFiniteType G.X.hom] in
/-- Weighted orbit integrals along parameters commuting with the subgroup `L` of the finite adelic
points preserve `L`-invariance. -/
theorem IsFiniteInvariant.weightedQuotientOrbitIntegral {h : C(Q, ℂ)}
    {L : Subgroup (FiniteAdelicGroupPoints F G)} (hh : IsFiniteInvariant F G T i h L)
    (b : C(Y, AdelicGroupPoints F G)) (w : C(Y, ℂ)) (hw : HasCompactSupport w)
    (hcomm : ∀ l ∈ L, ∀ y, AdelicGroupPoints.ofFinite F G l * b y =
      b y * AdelicGroupPoints.ofFinite F G l) :
    IsFiniteInvariant F G T i (weightedQuotientOrbitIntegral F G T i ν b w hw h) L :=
  fun l hl q => weightedQuotientOrbitIntegral_rightTranslate_of_commute F G T i ν b w hw h _
    (hcomm l hl) (hh l hl) q

end Invariance

section LevelInvariance

variable (K : Subgroup (FiniteAdelicGroupPoints F G)) [CompactSpace K] [MeasurableSpace K]
  [BorelSpace K]

/-- The finite adelic subgroup as parameters in the adelic group. -/
def levelParameter : C(K, AdelicGroupPoints F G) :=
  ⟨fun k => AdelicGroupPoints.ofFinite F G k.val,
    (AdelicGroupPoints.ofFinite F G).continuous.comp continuous_subtype_val⟩

omit [LocallyOfFiniteType G.X.hom] in
/-- Averaging over a compact subgroup with its left invariant measure makes a function invariant
under that subgroup. -/
theorem isFiniteInvariant_levelAverage (μK : Measure K) [IsFiniteMeasureOnCompacts μK]
    [μK.IsMulLeftInvariant] (h : C(Q, ℂ)) :
    IsFiniteInvariant F G T i (weightedQuotientOrbitIntegral F G T i μK (levelParameter F G K) 1
      (HasCompactSupport.of_compactSpace _) h) K := by
  intro l hl q
  obtain ⟨x, rfl⟩ := LeftCosetSpace.mk_surjective Γ q
  simp only [weightedQuotientOrbitIntegral_apply, LeftCosetSpace.rightTranslate_mk,
    ContinuousMap.one_apply, one_mul]
  let φ : K → ℂ := fun k => h (LeftCosetSpace.mk Γ (x * levelParameter F G K k))
  rw [← (integral_mul_left_eq_self φ ⟨l, hl⟩ :
    (∫ k, φ (⟨l, hl⟩ * k) ∂μK) = ∫ k, φ k ∂μK)]
  congr 1
  funext k
  simp only [φ, levelParameter, ContinuousMap.coe_mk, Subgroup.coe_mul, map_mul, mul_assoc]

end LevelInvariance

variable (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I]
  (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
  [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant]

local notation "ρ" => haarQuotientL2BoundedRightAction F G T i hi I e hc

/-- A nonzero vector of `A` with a continuous representative that satisfies a compact
conjugate mass bound and is invariant under the subgroup `L` of the finite adelic points. -/
structure IsRegularVector (A : Submodule ℂ (Lp ℂ 2 μQ))
    (L : Subgroup (FiniteAdelicGroupPoints F G)) (u : Lp ℂ 2 μQ) : Prop where
  mem : u ∈ A
  ne_zero : u ≠ 0
  rep : ∃ (h : C(Q, ℂ)) (S : Set (AdelicGroupPoints F G)) (C : ℝ), IsCompact S ∧ 0 ≤ C ∧
    (u : Q → ℂ) =ᵐ[μQ] h ∧ QuotientMassBound F G T i hi I e hc h S C ∧
      IsFiniteInvariant F G T i h L

theorem continuous_orbit (φ : Lp ℂ 2 μQ) : Continuous fun g : AdelicGroupPoints F G => ρ g φ :=
  (haarQuotientL2OrbitMap F G T i hi I e hc φ).continuous

/-- The vectors moved little by `ρ` form a neighbourhood of the identity. -/
theorem orbit_near_mem_nhds (φ : Lp ℂ 2 μQ) {ε : ℝ} (hε : 0 < ε) :
    {g : AdelicGroupPoints F G | ‖ρ g φ - φ‖ < ε} ∈ 𝓝 (1 : AdelicGroupPoints F G) := by
  apply ((continuous_orbit F G T i hi I e hc φ).sub continuous_const).norm.isOpen_preimage _
    isOpen_Iio |>.mem_nhds
  change ‖ρ 1 φ - φ‖ < ε
  rw [map_one, one_apply_eq_self, sub_self, norm_zero]
  exact hε

section Convolution

/-- **A nonzero regular vector.** Given the continuous-representative theorem for compact
convolution, every nonzero closed invariant subspace contains a nonzero vector with a continuous
representative satisfying a compact mass bound: convolve a nonzero vector with a normalized
bump near the identity. -/
theorem exists_isRegularVector_convolution
    (hrep : GroupSchemeQuotientL2ContinuousRepresentativeStatement.{u})
    (A : Submodule ℂ (Lp ℂ 2 μQ)) (hAc : IsClosed (A : Set (Lp ℂ 2 μQ)))
    (hAinv : ∀ g, ∀ φ ∈ A, ρ g φ ∈ A) {x₀ : Lp ℂ 2 μQ} (hx₀ : x₀ ∈ A) (hne : x₀ ≠ 0) :
    ∃ u, IsRegularVector F G T i hi I e hc A ⊥ u := by
  have hpos : 0 < ‖x₀‖ / 2 := half_pos (norm_pos_iff.mpr hne)
  obtain ⟨a, hacs, hasupp, ha1, hn⟩ := exists_normalized_bump
    (Measure.haar : Measure (AdelicGroupPoints F G)) 1 (orbit_near_mem_nhds F G T i hi I e hc x₀ hpos)
  let f : C_c(AdelicGroupPoints F G, ℂ) := ⟨a, hacs⟩
  have hf : Integrable f (Measure.haar : Measure (AdelicGroupPoints F G)) :=
    a.continuous.integrable_of_hasCompactSupport hacs
  have hint := haarQuotientL2ActionIntegrand_integrable F G T i hi I e hc Measure.haar f hf x₀
  obtain ⟨ψ, C, hC, hae, hMB⟩ := exists_quotientMassBound_representative F G T i hi I e hc hrep f hf x₀
  refine ⟨_, ⟨?_, ?_, ψ, _, C, f.hasCompactSupport.mul f.hasCompactSupport.inv, hC, hae, hMB,
    isFiniteInvariant_bot F G T i ψ⟩⟩
  · rw [haarQuotientL2IntegratedAction_apply]
    exact integral_mem_of_isClosed A hAc hint fun g => A.smul_mem _ (hAinv g x₀ hx₀)
  · rw [haarQuotientL2IntegratedAction_apply]
    exact integral_smul_ne_zero (fun g => f g) (fun g => ρ g x₀) x₀ hne hint hf ha1 hn
      fun g hg => (hasupp g hg).le

end Convolution

section Level

variable (K : Subgroup (FiniteAdelicGroupPoints F G)) [CompactSpace K] [MeasurableSpace K]
  [BorelSpace K]

omit [CompactSpace K] [MeasurableSpace K] [BorelSpace K] in
theorem continuous_levelParameter_orbit (φ : Lp ℂ 2 μQ) :
    Continuous fun k : K => ρ (levelParameter F G K k) φ :=
  (continuous_orbit F G T i hi I e hc φ).comp (levelParameter F G K).continuous

variable [SecondCountableTopology K] [IsTopologicalGroup K]

/-- **Averaging over a compact finite level.** Averaging a regular vector over a compact
subgroup of the finite adelic points, on which its orbit stays within half its norm, gives a
regular vector invariant under that subgroup. -/
theorem isRegularVector_levelAverage (A : Submodule ℂ (Lp ℂ 2 μQ))
    (hAc : IsClosed (A : Set (Lp ℂ 2 μQ))) (hAinv : ∀ g, ∀ φ ∈ A, ρ g φ ∈ A)
    {L' : Subgroup (FiniteAdelicGroupPoints F G)} {u : Lp ℂ 2 μQ}
    (hu : IsRegularVector F G T i hi I e hc A L' u)
    (hK : ∀ k : K, ‖ρ (levelParameter F G K k) u - u‖ ≤ ‖u‖ / 2) :
    IsRegularVector F G T i hi I e hc A K
      (∫ k, (1 : C(K, ℂ)) k • ρ (levelParameter F G K k) u ∂(Langlands.Analysis.compactProbabilityHaar K)) := by
  obtain ⟨h, S, C, hS, hC, hae, hMB, -⟩ := hu.rep
  let μK := Langlands.Analysis.compactProbabilityHaar K
  obtain ⟨hint, hae'⟩ := groupSchemeQuotientL2IntegratedRepresentative F G T i hi I e hc μK
    (levelParameter F G K) 1 (HasCompactSupport.of_compactSpace _) u h hae
  have hint' : Integrable (fun k => (1 : C(K, ℂ)) k • ρ (levelParameter F G K k) u) μK := hint
  refine ⟨integral_mem_of_isClosed A hAc hint' fun k => A.smul_mem _ (hAinv _ u hu.mem), ?_,
    weightedQuotientOrbitIntegral F G T i μK (levelParameter F G K) 1
      (HasCompactSupport.of_compactSpace _) h, _, _,
    isCompact_conjugateSet F G ((HasCompactSupport.of_compactSpace (1 : C(K, ℂ))).isCompact.image
      (levelParameter F G K).continuous) hS,
    mul_nonneg hC (sq_nonneg _), hae',
    quotientMassBound_weightedQuotientOrbitIntegral F G T i hi I e hc μK _ _ _ h hS hC hMB,
    isFiniteInvariant_levelAverage F G T i K μK h⟩
  have hone : Integrable (fun k : K => ((1 : C(K, ℂ)) k)) μK := integrable_const _
  apply integral_smul_ne_zero (fun k => (1 : C(K, ℂ)) k) (fun k => ρ (levelParameter F G K k) u)
    u hu.ne_zero hint' hone
  · simp only [ContinuousMap.one_apply, integral_const, probReal_univ, one_smul]
  · simp only [ContinuousMap.one_apply, norm_one, integral_const, probReal_univ, one_smul]
  · exact fun k _ => hK k

/-- **A regular vector at a compact open level.** A regular vector of a closed invariant subspace
gives a regular vector invariant under some compact open subgroup of the finite adelic points. -/
theorem exists_isRegularVector_level (A : Submodule ℂ (Lp ℂ 2 μQ))
    (hAc : IsClosed (A : Set (Lp ℂ 2 μQ))) (hAinv : ∀ g, ∀ φ ∈ A, ρ g φ ∈ A)
    {L' : Subgroup (FiniteAdelicGroupPoints F G)} {u : Lp ℂ 2 μQ}
    (hu : IsRegularVector F G T i hi I e hc A L' u) :
    ∃ K : OpenSubgroup (FiniteAdelicGroupPoints F G),
      IsCompact (K : Set (FiniteAdelicGroupPoints F G)) ∧
        ∃ u₁, IsRegularVector F G T i hi I e hc A K.toSubgroup u₁ := by
  have hpos : 0 < ‖u‖ / 2 := half_pos (norm_pos_iff.mpr hu.ne_zero)
  have hU : (AdelicGroupPoints.ofFinite F G) ⁻¹' {g | ‖ρ g u - u‖ < ‖u‖ / 2} ∈
      𝓝 (1 : FiniteAdelicGroupPoints F G) := by
    have h1 : AdelicGroupPoints.ofFinite F G 1 = 1 := map_one _
    refine ContinuousAt.preimage_mem_nhds (f := AdelicGroupPoints.ofFinite F G)
      (AdelicGroupPoints.ofFinite F G).continuous.continuousAt ?_
    rw [h1]
    exact orbit_near_mem_nhds F G T i hi I e hc u hpos
  have hb := (finiteAdelicGroupCompactOpenBasis F G).2
  obtain ⟨K, hKc, hKU⟩ := hb.mem_iff.mp hU
  let : MeasurableSpace K.toSubgroup := borel _
  have : BorelSpace K.toSubgroup := ⟨rfl⟩
  have : CompactSpace K.toSubgroup := isCompact_iff_compactSpace.mp hKc
  have : SecondCountableTopology K.toSubgroup :=
    TopologicalSpace.secondCountableTopology_induced _ (FiniteAdelicGroupPoints F G)
      (fun k : K.toSubgroup => (k : FiniteAdelicGroupPoints F G))
  exact ⟨K, hKc, _, isRegularVector_levelAverage F G T i hi I e hc K.toSubgroup A hAc hAinv hu
    fun k => (hKU k.property).le⟩

end Level

end Langlands.Automorphic.GroupSchemeFunctions

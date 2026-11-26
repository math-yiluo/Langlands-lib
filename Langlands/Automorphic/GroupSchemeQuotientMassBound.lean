import Langlands.Automorphic.GeneralLinearContinuousSmoothingGrowth
import Langlands.Automorphic.GroupSchemeQuotientL2IntegratedRepresentative

/-! # Conjugate subgroup mass bounds for continuous functions on the positive quotient -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry MeasureTheory NumberField Set Topology
open scoped CategoryTheory.MonObj CompactlySupported Pointwise

set_option autoImplicit false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme

section MassBound

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
  (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I]
  (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)

local notation "Q" => PositiveRationalQuotient F G T i
local notation "Γ" => positiveRationalSubgroup F G T i
local notation "μH" => positiveRationalSubgroupHaarMeasure F G T i hi I e hc

/-- The positive rational subgroup mass of the conjugate `x S x⁻¹`. -/
def conjugateMass (S : Set (AdelicGroupPoints F G)) (x : AdelicGroupPoints F G) : ℝ :=
  (μH).real (Subtype.val ⁻¹' ((fun s => x * s * x⁻¹) '' S))

/-- A function on the quotient satisfies the conjugate mass bound for `S` and `C` when the
square of its norm at the coset of `x` is at most `C` times the positive rational subgroup
mass of `x S x⁻¹`. -/
def QuotientMassBound (h : Q → ℂ) (S : Set (AdelicGroupPoints F G)) (C : ℝ) : Prop :=
  ∀ x : AdelicGroupPoints F G,
    ‖h (LeftCosetSpace.mk Γ x)‖ ^ 2 ≤ C * conjugateMass F G T i hi I e hc S x

theorem conjugateMass_nonneg (S : Set (AdelicGroupPoints F G)) (x : AdelicGroupPoints F G) :
    0 ≤ conjugateMass F G T i hi I e hc S x :=
  measureReal_nonneg

/-- The subgroup mass of a compact conjugate is finite. -/
theorem conjugateMass_ne_top (S : Set (AdelicGroupPoints F G)) (hS : IsCompact S)
    (x : AdelicGroupPoints F G) :
    (μH) (Subtype.val ⁻¹' ((fun s => x * s * x⁻¹) '' S)) ≠ ⊤ := by
  have := positiveRationalSubgroupHaarMeasure_isHaarMeasure F G T i hi I e hc
  have hK : IsCompact ((fun s => x * s * x⁻¹) '' S) :=
    hS.image ((continuous_const.mul continuous_id).mul continuous_const)
  have hK' : IsCompact (Subtype.val ⁻¹' ((fun s => x * s * x⁻¹) '' S) : Set Γ) :=
    (isClosed_positiveRationalSubgroup F G T i hi I e hc).isClosedEmbedding_subtypeVal
      |>.isCompact_preimage hK
  exact hK'.measure_lt_top.ne

/-- Conjugate masses are monotone when the larger conjugate is compact. -/
theorem conjugateMass_le_of_subset {S S' : Set (AdelicGroupPoints F G)} (hS' : IsCompact S')
    {x y : AdelicGroupPoints F G}
    (hsub : (fun s => y * s * y⁻¹) '' S ⊆ (fun s => x * s * x⁻¹) '' S') :
    conjugateMass F G T i hi I e hc S y ≤ conjugateMass F G T i hi I e hc S' x :=
  measureReal_mono (preimage_mono hsub) (conjugateMass_ne_top F G T i hi I e hc S' hS' x)

omit [LocallyOfFiniteType G.X.hom] in
/-- The compact set `B S B⁻¹` attached to a parameter set `B`. -/
theorem isCompact_conjugateSet {B S : Set (AdelicGroupPoints F G)} (hB : IsCompact B)
    (hS : IsCompact S) : IsCompact (B * S * B⁻¹) :=
  (hB.mul hS).mul hB.inv

section Orbit

variable {Y : Type v} [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
  (ν : Measure Y) [IsFiniteMeasureOnCompacts ν]

/-- **Weighted orbit integrals preserve conjugate mass bounds.** If `h` satisfies the mass
bound for a compact set `S` and `C ≥ 0`, its integral against a compactly supported weight `w`
along a continuous parameter `b` satisfies the mass bound for `B S B⁻¹`, `B = b(supp w)`, with
constant `C (∫ ‖w‖)²`. -/
theorem quotientMassBound_weightedQuotientOrbitIntegral (b : C(Y, AdelicGroupPoints F G))
    (w : C(Y, ℂ)) (hw : HasCompactSupport w) (h : C(Q, ℂ)) {S : Set (AdelicGroupPoints F G)}
    (hS : IsCompact S) {C : ℝ} (hC : 0 ≤ C) (hh : QuotientMassBound F G T i hi I e hc h S C) :
    QuotientMassBound F G T i hi I e hc (weightedQuotientOrbitIntegral F G T i ν b w hw h)
      ((b '' tsupport w) * S * (b '' tsupport w)⁻¹) (C * (∫ y, ‖w y‖ ∂ν) ^ 2) := by
  intro x
  let B := b '' tsupport w
  have hB : IsCompact B := hw.isCompact.image b.continuous
  let m := conjugateMass F G T i hi I e hc (B * S * B⁻¹) x
  have hm : 0 ≤ m := conjugateMass_nonneg F G T i hi I e hc _ x
  have hpt (y : Y) (hy : y ∈ tsupport w) :
      ‖h (LeftCosetSpace.mk Γ (x * b y))‖ ≤ Real.sqrt (C * m) := by
    apply Real.le_sqrt_of_sq_le
    refine (hh (x * b y)).trans (mul_le_mul_of_nonneg_left ?_ hC)
    apply conjugateMass_le_of_subset F G T i hi I e hc (isCompact_conjugateSet F G hB hS)
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨b y * s * (b y)⁻¹, ⟨b y * s, ⟨b y, ⟨y, hy, rfl⟩, s, hs, rfl⟩, (b y)⁻¹,
      ⟨y, hy, (inv_inv _).symm⟩, rfl⟩, ?_⟩
    simp only [mul_inv_rev, mul_assoc]
  have hwI : Integrable (fun y => ‖w y‖) ν :=
    (w.continuous.integrable_of_hasCompactSupport hw).norm
  have hbound : ‖weightedQuotientOrbitIntegral F G T i ν b w hw h (LeftCosetSpace.mk Γ x)‖ ≤
      Real.sqrt (C * m) * ∫ y, ‖w y‖ ∂ν := by
    rw [weightedQuotientOrbitIntegral_apply, ← integral_const_mul]
    refine norm_integral_le_of_norm_le (hwI.const_mul _) (Filter.Eventually.of_forall fun y => ?_)
    rw [norm_mul, LeftCosetSpace.rightTranslate_mk, mul_comm (Real.sqrt (C * m))]
    by_cases hy : y ∈ tsupport w
    · exact mul_le_mul_of_nonneg_left (hpt y hy) (norm_nonneg _)
    · rw [image_eq_zero_of_notMem_tsupport hy, norm_zero, zero_mul, zero_mul]
  calc ‖weightedQuotientOrbitIntegral F G T i ν b w hw h (LeftCosetSpace.mk Γ x)‖ ^ 2
      ≤ (Real.sqrt (C * m) * ∫ y, ‖w y‖ ∂ν) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hbound 2
    _ = C * (∫ y, ‖w y‖ ∂ν) ^ 2 * m := by
        rw [mul_pow, Real.sq_sqrt (mul_nonneg hC hm)]
        ring

end Orbit

variable [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant]

/-- Given the continuous-representative theorem for compact convolution, every convolution
class has a continuous representative with a conjugate mass bound for the compact set
`supp f · (supp f)⁻¹`. -/
theorem exists_quotientMassBound_representative
    (hrep : GroupSchemeQuotientL2ContinuousRepresentativeStatement.{u})
    (f : C_c(AdelicGroupPoints F G, ℂ))
    (hf : Integrable f (Measure.haar : Measure (AdelicGroupPoints F G)))
    (φ : Lp ℂ 2 (positiveRationalQuotientHaarMeasure F G T i)) :
    ∃ (ψ : C(Q, ℂ)) (C : ℝ), 0 ≤ C ∧
      (haarQuotientL2IntegratedAction F G T i hi I e hc Measure.haar f hf φ : Q → ℂ)
        =ᵐ[positiveRationalQuotientHaarMeasure F G T i] ψ ∧
      QuotientMassBound F G T i hi I e hc ψ (tsupport f * (tsupport f)⁻¹) C := by
  obtain ⟨ψ, hψ, hψae, hψest⟩ := hrep F G T i hi I e hc f hf φ
  let K := tsupport f
  have hK : IsCompact K := f.hasCompactSupport
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn f.continuous.continuousOn
  let M' := max 0 M
  have hM' : 0 ≤ M' := le_max_left _ _
  have hbound (x : AdelicGroupPoints F G) : ‖f x‖ ≤ M' := by
    by_cases hx : x ∈ K
    · exact (hM x hx).trans (le_max_right _ _)
    · rw [image_eq_zero_of_notMem_tsupport hx, norm_zero]
      exact hM'
  let C := M' * (∫ a, ‖f a‖ ∂(Measure.haar : Measure (AdelicGroupPoints F G))) * ‖φ‖ ^ 2
  have hC : 0 ≤ C :=
    mul_nonneg (mul_nonneg hM' (integral_nonneg fun _ => norm_nonneg _)) (sq_nonneg _)
  refine ⟨⟨ψ, hψ⟩, C, hC, hψae, fun x => ?_⟩
  change ‖ψ (Quotient.mk _ x)‖ ^ 2 ≤ C * conjugateMass F G T i hi I e hc (K * K⁻¹) x
  dsimp only [C, conjugateMass]
  rw [mul_right_comm (M' * _)]
  exact hψest x M' hbound

end MassBound

section GeneralLinear

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)
  (T : CommGroupScheme (Spec (CommRingCat.of F)))
  (i : T.toGrp ⟶ GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F))
  (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I]
  (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)

private local instance (F : Type u) [Field F] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

private local instance (F : Type u) [Field F] (n : ℕ) :
    Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)

/-- On `GL_n`, a conjugate mass bound for a compact set gives polynomial growth on every
finite slice, with degree the real dimension of the archimedean matrices. -/
theorem QuotientMassBound.sliceGrowth
    {ψ : PositiveRationalQuotient F (GroupScheme.GeneralLinear.groupScheme (Fin n)
      (CommRingCat.of F)) T i → ℂ}
    {S : Set (AdelicGroupPoints F (GroupScheme.GeneralLinear.groupScheme (Fin n)
      (CommRingCat.of F)))} (hS : IsCompact S) {C : ℝ} (hC : 0 ≤ C)
    (hψ : QuotientMassBound F _ T i hi I e hc ψ S C) (b : FiniteAdelicGL F n) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ a : InfiniteAdelicGL F n,
      ‖ψ (LeftCosetSpace.mk _
        ((GeneralLinearGroupPoints.adelicHomeomorph F n).symm (AdelicGL.pair F n a b)))‖ ≤
        C' * infiniteAdelicHilbertNorm F n a ^ Module.finrank ℝ (ArchimedeanMatrix F n) :=
  generalLinear_sliceGrowth_of_compactConjugateBound F n T i hi I e hc S hS ψ C hC hψ b

end GeneralLinear

end Langlands.Automorphic.GroupSchemeFunctions

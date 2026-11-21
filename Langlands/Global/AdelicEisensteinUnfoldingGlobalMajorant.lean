import Langlands.Global.AdelicIntertwiningConvergenceReduction
import Langlands.Global.AdelicRepresentationHeightPropernessProof
import Langlands.Global.EisensteinConstantTerm.GeometricLemmaUnfoldingStatement

/-! # Global polynomial majorants on rational unipotent stabilizer quotients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Set
open scoped CategoryTheory.MonObj ENNReal

set_option autoImplicit false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme RepresentationGrowth Langlands.Automorphic.GroupSchemeFunctions

variable {F : Type u} [Field F] [NumberField F]
  {G P M U V : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [IsAffine P.X.left] [IsAffine V.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left]
  {iU : U ⟶ P} {l : M ⟶ P}
  {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K)
  (j : V ⟶ G) [IsClosedImmersion j.hom.hom.left]
  (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X)
  {N : ℕ} (rho : MatrixRepresentation G (Fin N))

local notation "Vₐ" => AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j)
local notation "Vᵣ" => AdelicSubgroupPoints.rationalSubgroup F G (SubgroupFunctor.range j)
local notation "wA" => innerAdelicPoint F G w

set_option maxHeartbeats 1200000 in
/-- Compact radical representatives convert a summable coset majorant into an
integrable quotient majorant while retaining the external polynomial weight. -/
theorem exists_integrable_unfolding_majorant
    (hN : 0 < N) (hV : Smooth V.X.hom) (hVc : ConnectedSpace V.X.left) (hVu : IsUnipotent V)
    (Λ : Subgroup Vₐ) (hΛ : IsDiscrete (Λ : Set Vₐ))
    (hClass : ∀ δ δ' : Vᵣ, intertwiningRationalCoset F p w δ = intertwiningRationalCoset F p w δ' →
      δ'.val * δ.val⁻¹ ∈ Λ)
    (hl : IsRationalLeviSubgroup l) (hU : LeviSubgroup.IsGeometricUnipotentRadical iU)
    (φ : AdelicGroupPoints F G → ℂ)
    (hinv : IsLeftInvariantUnder F G (parabolicQuotientSubgroup F p iU l) φ)
    (lam : ComplexCharacterParameter F P)
    (b : ParabolicRationalCosets F p → ℝ) (hb : Summable b) (hb0 : ∀ x, 0 ≤ b x)
    (d : ℝ) (hd : 0 ≤ d)
    (hbound : ∀ g x, ‖hK.eisensteinTerm φ lam g x‖ ≤ b x * adelicHeight F G rho g ^ d) :
    let hClosed := AdelicSubgroupPoints.isClosed_adelicPoints_range F G j
    haveI : IsClosed (Vₐ : Set (AdelicGroupPoints F G)) := hClosed
    let ν := AdelicSubgroupPoints.normalizedHaarMeasure F G (SubgroupFunctor.range j)
    ∃ B : LeftCosetSpace Λ → ℝ,
      Integrable B (LeftCosetSpace.discreteQuotientMeasure Λ hΛ ν) ∧ (∀ x, 0 ≤ B x) ∧
      ∀ x g, ‖hK.parameterTwist φ lam (wA⁻¹ * (Quotient.out x : Vₐ).val * g)‖ ≤
        B x * adelicHeight F G rho g ^ d := by
  intro hClosed ν
  let : IsClosed (Vₐ : Set (AdelicGroupPoints F G)) := hClosed
  let : LocallyCompactSpace Vₐ := hClosed.locallyCompactSpace
  let : PolishSpace Vₐ := hClosed.polishSpace
  let : CompactSpace (AdelicSubgroupPoints.RationalQuotient F G (SubgroupFunctor.range j)) :=
    AdelicSubgroupPoints.compactSpace_rationalQuotient_range_unipotent F j hV hVc hVu
  let : ν.IsHaarMeasure := Measure.IsHaarMeasure.smul _
    (AdelicSubgroupPoints.quotientMassNormalizer_ne_zero F G (SubgroupFunctor.range j))
    (AdelicSubgroupPoints.quotientMassNormalizer_ne_top F G (SubgroupFunctor.range j))
  let : Countable (rationalSubgroup F G) :=
    LeftCosetSpace.countable_of_isDiscrete _ (isDiscrete_rationalSubgroup F G)
  obtain ⟨Ω, hΩ, hCover⟩ := AdelicSubgroupPoints.exists_isCompact_rational_mul_mem_range F j hV hVc hVu
  let H := adelicHeight F G rho
  obtain ⟨D, hD⟩ := ((hΩ.image continuous_subtype_val).image (continuous_adelicHeight F G rho hN)).bddAbove
  let L := max D 1
  have hL : 0 < L := zero_lt_one.trans_le (le_max_right _ _)
  obtain ⟨B₀, hB₀, hB⟩ := LeftCosetSpace.exists_integrable_majorant_of_cover
    Vᵣ Λ hΛ ν hΩ hΩ.measure_lt_top.ne (intertwiningRationalCoset F p w) hClass
    (hb.mul_left (L ^ d))
  refine ⟨fun x => ‖B₀ x‖, hB₀.norm, fun x => norm_nonneg _, fun x g => ?_⟩
  obtain ⟨v, hv, hΩv⟩ := hCover (Quotient.out x)
  let δ : Vᵣ := ⟨v⁻¹, inv_mem hv⟩
  let z : Vₐ := v * Quotient.out x
  have hx : LeftCosetSpace.mk Λ (δ.val * z) = x := by
    change LeftCosetSpace.mk Λ (v⁻¹ * (v * Quotient.out x)) = x
    rw [inv_mul_cancel_left]
    exact Quotient.out_eq x
  have hz : H z.val ≤ L :=
    (hD ⟨z.val, ⟨z, hΩv, rfl⟩, rfl⟩).trans (le_max_left _ _)
  have hHg : 0 ≤ H g := zero_le_one.trans (one_le_adelicHeight F G rho hN g)
  have hZg : H (z.val * g) ≤ L * H g :=
    (adelicHeight_mul_le F G rho hN _ _).trans (mul_le_mul_of_nonneg_right hz hHg)
  have hβ := hB δ z hΩv
  rw [hx] at hβ
  have hAt := hbound (z.val * g) (intertwiningRationalCoset F p w δ)
  rw [intertwiningRationalCoset, hK.eisensteinTerm_mk hinv hl hU] at hAt
  have heq : wA⁻¹ * (Quotient.out x : Vₐ).val * g =
      (wA⁻¹ * δ.val.val) * (z.val * g) := by
    dsimp [δ, z]
    group
  rw [heq]
  refine hAt.trans ?_
  calc
    _ ≤ b (intertwiningRationalCoset F p w δ) * (L * H g) ^ d :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow
        (zero_le_one.trans (one_le_adelicHeight F G rho hN _)) hZg hd) (hb0 _)
    _ = (L ^ d * b (intertwiningRationalCoset F p w δ)) * H g ^ d := by
      rw [Real.mul_rpow hL.le hHg]
      ring
    _ ≤ _ :=
      mul_le_mul_of_nonneg_right ((show L ^ d * b (intertwiningRationalCoset F p w δ) ≤ B₀ x
        from hβ).trans (by
          change B₀ x ≤ ‖B₀ x‖
          rw [Real.norm_eq_abs]
          exact le_abs_self _)) (Real.rpow_nonneg hHg _)

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [IsAffine P.X.left]
  [IsAffine V.X.left] [IsClosedImmersion p.hom.hom.left] [IsClosedImmersion j.hom.hom.left] in
/-- The fibres used to unfold rational radical translates lie in single
cosets of the full rational parabolic stabilizer. -/
theorem intertwiningRationalCoset_fiber_le_stabilizer
    (δ δ' : Vᵣ) (he : intertwiningRationalCoset F p w δ = intertwiningRationalCoset F p w δ') :
    δ'.val * δ.val⁻¹ ∈ stabilizerRationalSubgroup F p j wA := by
  have hr := QuotientGroup.rightRel_apply.mp (Quotient.exact he)
  rw [parabolicRationalSubgroup, Subgroup.mem_subgroupOf] at hr
  obtain ⟨_, ⟨y, rfl⟩, hy⟩ := hr
  rw [mem_stabilizerRationalSubgroup_iff]
  refine ⟨mul_mem δ'.property (inv_mem δ.property), ⟨y, ?_⟩⟩
  change map F P G p (rational F P y) = wA⁻¹ * (δ'.val * δ.val⁻¹).val * wA
  change map F P G p (rational F P y) = (wA⁻¹ * δ'.val.val) * (wA⁻¹ * δ.val.val)⁻¹ at hy
  rw [hy]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  group

/-- The global summable bound for the original Eisenstein terms gives a
polynomial-weighted integrable majorant on the full rational stabilizer
quotient in the geometric unfolding. -/
def EisensteinUnfoldingGlobalMajorantStatement (iU : U ⟶ P) (l : M ⟶ P) : Prop :=
  0 < N → Smooth V.X.hom → ConnectedSpace V.X.left → IsUnipotent V →
  IsRationalLeviSubgroup l → LeviSubgroup.IsGeometricUnipotentRadical iU →
  ∀ (φ : AdelicGroupPoints F G → ℂ),
    IsLeftInvariantUnder F G (parabolicQuotientSubgroup F p iU l) φ →
    ∀ (lam : ComplexCharacterParameter F P)
      (b : ParabolicRationalCosets F p → ℝ) (d : ℝ),
      Summable b → (∀ x, 0 ≤ b x) → 0 ≤ d →
      (∀ g x, ‖hK.eisensteinTerm φ lam g x‖ ≤ b x * adelicHeight F G rho g ^ d) →
      ∃ B : LeftCosetSpace (stabilizerRationalSubgroup F p j wA) → ℝ,
        Integrable B (stabilizerMeasure F p j wA) ∧ (∀ x, 0 ≤ B x) ∧
        ∀ x g, ‖hK.parameterTwist φ lam (wA⁻¹ * (Quotient.out x : Vₐ).val * g)‖ ≤
          B x * adelicHeight F G rho g ^ d

theorem eisensteinUnfoldingGlobalMajorant :
    EisensteinUnfoldingGlobalMajorantStatement hK j w rho iU l := by
  intro hN hV hVc hVu hl hU φ hinv lam b d hb hb0 hd hbound
  exact exists_integrable_unfolding_majorant hK j w rho hN hV hVc hVu
    (stabilizerRationalSubgroup F p j wA) (isDiscrete_stabilizerRationalSubgroup F p j wA)
    (intertwiningRationalCoset_fiber_le_stabilizer j w) hl hU φ hinv lam b hb hb0 d hd hbound

end Langlands.Global.AdelicGroupPoints

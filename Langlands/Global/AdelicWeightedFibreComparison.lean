import Langlands.Global.AdelicWeightedSiegelSpace
import Langlands.Global.NestedLeftCosetIntegral
import Mathlib.Data.Set.Card

/-! # Weighted measure comparison from fibre bounds -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open AlgebraicGeometry CategoryTheory MeasureTheory Set
open scoped CategoryTheory.MonObj ENNReal

namespace Langlands.Global.WeightedSiegel

open AdelicGroupPoints LeftCosetSpace Langlands.Automorphic.GroupSchemeFunctions

variable {F : Type u} [Field F] [NumberField F]
  {G P : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [IsAffine P.X.left]
  [LocallyOfFiniteType G.X.hom] {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left]
  {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K)

local notation "A" => AdelicGroupPoints F G
local notation "Γ" => parabolicPrincipalSubgroup F p
local notation "Λ" => rationalSubgroup F G
local notation "Z" => DomainQuotient F p
local notation "X" => RationalQuotient F G
local notation "I" => LeftCosetSpace (Subgroup.comap (Subgroup.subtype Λ) Γ)
local notation "π" => toAutomorphic F p
local notation "Hₚ" => domainHeight F p hK
local notation "μG" => (Measure.haar : Measure A)

omit [IsAffine G.X.left] [IsAffine P.X.left] [LocallyOfFiniteType G.X.hom]
  [IsClosedImmersion p.hom.hom.left] in
private theorem toAutomorphic_mk_mul (x : A) (c : I) :
    π (mk Γ (c.out.val * x)) = mk Λ x := by
  rw [toAutomorphic_mk, mk_subgroup_mul Λ c.out]

omit [IsAffine G.X.left] [IsAffine P.X.left] [LocallyOfFiniteType G.X.hom]
  [IsClosedImmersion p.hom.hom.left] in
private theorem exists_mk_cosetRepresentative_mul (x : A) (z : Z) (hz : π z = mk Λ x) :
    ∃ c : I, mk Γ (c.out.val * x) = z := by
  obtain ⟨y, rfl⟩ := mk_surjective Γ z
  let a : Λ := ⟨y * x⁻¹, (mk_eq_mk_iff Λ x y).mp hz.symm⟩
  let c : I := mk (Subgroup.comap (Subgroup.subtype Λ) Γ) a
  refine ⟨c, ?_⟩
  have h := (mk_mul_subtype_eq_iff Γ Λ c.out a x).mpr (Quotient.out_eq c)
  have hay : a.val * x = y := by simp [a, mul_assoc]
  rwa [hay] at h

private theorem lintegral_automorphicMeasure_eq_cosetSum
    (ell : RealCharacterDual F P → ℝ) (hell : Continuous ell)
    (S : Set Z) (hS : MeasurableSet S) {φ : X → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ y, φ y ∂automorphicMeasure F p hK ell S =
      ∫⁻ x in fundamentalDomain Λ (isDiscrete_rationalSubgroup F G),
        φ (mk Λ x) * (∑' c : I, S.indicator (domainDensity F p hK ell) (mk Γ (c.out.val * x))) ∂μG := by
  let δ := domainDensity F p hK ell
  have hπ : Measurable π := (continuous_toAutomorphic F p).measurable
  have hδ : Measurable δ := measurable_domainDensity F p hK hell
  let hΛ := isDiscrete_rationalSubgroup F G
  let hle := parabolicPrincipalSubgroup_le F p
  rw [automorphicMeasure, lintegral_map hφ hπ, domainMeasure]
  change ∫⁻ z, (φ ∘ π) z ∂((domainHaarMeasure F p).restrict S).withDensity δ = _
  rw [lintegral_withDensity_eq_lintegral_mul _ hδ (hφ.comp hπ), ← lintegral_indicator hS]
  change ∫⁻ z, S.indicator (δ * (φ ∘ π)) z ∂discreteQuotientMeasure Γ (hΛ.mono hle) μG = _
  rw [nestedLeftCosetIntegral Γ Λ hle hΛ μG _ ((hδ.mul (hφ.comp hπ)).indicator hS)]
  apply lintegral_congr
  intro x
  rw [← ENNReal.tsum_mul_left]
  congr 1
  funext c
  let z := mk Γ (c.out.val * x)
  have hz : π z = mk Λ x := toAutomorphic_mk_mul x c
  change S.indicator (δ * fun q => φ (π q)) z = φ (mk Λ x) * S.indicator δ z
  by_cases h : z ∈ S
  · simp only [indicator_of_mem h, Pi.mul_apply, hz, mul_comm]
  · simp only [indicator_of_notMem h, mul_zero]

/-- Point-count and log-weight comparison on the fibres give a domination of the
pushforward measures from two measurable regions. -/
def WeightedFibreComparisonStatement : Prop :=
  ∀ (ell : RealCharacterDual F P → ℝ), Continuous ell →
  ∀ (S₀ S : Set Z), MeasurableSet S₀ → MeasurableSet S →
  (∀ y : X, ∃ z ∈ S₀, π z = y) →
  ∀ (N : ℕ) (d : ℝ),
  (∀ y : X, {z ∈ S | π z = y}.encard ≤ N) →
  (∀ z₀ ∈ S₀, ∀ z ∈ S, π z₀ = π z → ell (Hₚ z₀) - ell (Hₚ z) ≤ d) →
  automorphicMeasure F p hK ell S ≤
    ENNReal.ofReal (N * Real.exp (2 * d)) • automorphicMeasure F p hK ell S₀

theorem weightedFibreComparison : WeightedFibreComparisonStatement hK := by
  classical
  intro ell hell S₀ S hS₀ hS hcover N d hcount hweight
  let δ := domainDensity F p hK ell
  let C := ENNReal.ofReal (N * Real.exp (2 * d))
  have hC : C = (N : ℝ≥0∞) * ENNReal.ofReal (Real.exp (2 * d)) := by
    simp [C, ENNReal.ofReal_mul (Nat.cast_nonneg N)]
  have hsum (x : A) :
      (∑' c : I, S.indicator δ (mk Γ (c.out.val * x))) ≤
        C * (∑' c : I, S₀.indicator δ (mk Γ (c.out.val * x))) := by
    let f (c : I) := mk Γ (c.out.val * x)
    let U := f ⁻¹' S
    have hf (c : I) : π (f c) = mk Λ x := toAutomorphic_mk_mul x c
    obtain ⟨z₀, hz₀, hz₀x⟩ := hcover (mk Λ x)
    obtain ⟨c₀, hc₀⟩ := exists_mk_cosetRepresentative_mul x z₀ hz₀x
    have hlower : δ z₀ ≤ ∑' c : I, S₀.indicator δ (f c) := by
      change f c₀ = z₀ at hc₀
      simpa only [hc₀, indicator_of_mem hz₀] using ENNReal.le_tsum (f := fun c => S₀.indicator δ (f c)) c₀
    have hU : U.encard ≤ N := (encard_le_encard_of_injOn
      (show MapsTo f U {z ∈ S | π z = mk Λ x} from fun c hc => ⟨hc, hf c⟩)
      (injective_mk_cosetRepresentative_mul Γ Λ x).injOn).trans (hcount _)
    obtain ⟨hfin, hcard⟩ := encard_le_coe_iff_finite_ncard_le.mp hU
    let V := hfin.toFinset
    have hV : V.card ≤ N := by simpa only [V, ← ncard_eq_toFinset_card _ hfin] using hcard
    have hbound (c : I) (hc : c ∈ V) :
        S.indicator δ (f c) ≤ ENNReal.ofReal (Real.exp (2 * d)) * δ z₀ := by
      have hfc : f c ∈ S := hfin.mem_toFinset.mp hc
      rw [indicator_of_mem hfc]
      dsimp [δ, domainDensity]
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
      have h := hweight z₀ hz₀ (f c) hfc (hz₀x.trans (hf c).symm)
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith))
    change (∑' c : I, S.indicator δ (f c)) ≤ C * (∑' c : I, S₀.indicator δ (f c))
    calc
      _ = ∑ c ∈ V, S.indicator δ (f c) := by
        apply tsum_eq_sum
        intro c hc
        exact indicator_of_notMem (s := S) (a := f c)
          (fun hh => hc (hfin.mem_toFinset.mpr hh)) δ
      _ ≤ ∑ _c ∈ V, ENNReal.ofReal (Real.exp (2 * d)) * δ z₀ := Finset.sum_le_sum hbound
      _ = (V.card : ℝ≥0∞) * (ENNReal.ofReal (Real.exp (2 * d)) * δ z₀) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (N : ℝ≥0∞) * (ENNReal.ofReal (Real.exp (2 * d)) * δ z₀) := by gcongr
      _ = C * δ z₀ := by rw [hC, mul_assoc]
      _ ≤ _ := by gcongr
  apply Measure.le_iff.mpr
  intro W hW
  let D₀ := fundamentalDomain Λ (isDiscrete_rationalSubgroup F G)
  let f₀ (x : A) := W.indicator (1 : X → ℝ≥0∞) (mk Λ x) *
    (∑' c : I, S₀.indicator δ (mk Γ (c.out.val * x)))
  let f (x : A) := W.indicator (1 : X → ℝ≥0∞) (mk Λ x) *
    (∑' c : I, S.indicator δ (mk Γ (c.out.val * x)))
  rw [Measure.smul_apply, smul_eq_mul]
  change automorphicMeasure F p hK ell S W ≤ C * automorphicMeasure F p hK ell S₀ W
  have hWmeas : Measurable (W.indicator (1 : X → ℝ≥0∞)) :=
    (show Measurable (1 : X → ℝ≥0∞) from measurable_const).indicator hW
  have hM (T : Set Z) (hT : MeasurableSet T) :=
    lintegral_automorphicMeasure_eq_cosetSum hK ell hell T hT hWmeas
  rw [← lintegral_indicator_one («μ» := automorphicMeasure F p hK ell S) hW, hM S hS,
    ← lintegral_indicator_one («μ» := automorphicMeasure F p hK ell S₀) hW, hM S₀ hS₀]
  change (∫⁻ x in D₀, f x ∂μG) ≤ C * ∫⁻ x in D₀, f₀ x ∂μG
  rw [← lintegral_const_mul' C f₀ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro x
  dsimp only [f, f₀]
  rw [mul_left_comm]
  gcongr
  exact hsum x

end Langlands.Global.WeightedSiegel

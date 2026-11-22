import Langlands.Global.AdelicWeightedSmoothingOperator
import Mathlib.LinearAlgebra.Dimension.LinearMap

/-! # Measurable realizations of the weighted automorphic Hilbert space -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open AlgebraicGeometry CategoryTheory MeasureTheory Set
open scoped CategoryTheory.MonObj ENNReal

namespace Langlands.Global.WeightedSiegel

open AdelicGroupPoints Langlands.Automorphic.GroupSchemeFunctions

private theorem exists_measurableLp_section {X : Type u} [MeasurableSpace X] (m : Measure X) :
    ∃ s : Lp ℂ 2 m →ₗ[ℂ] (X → ℂ), ∀ v, Measurable (s v) ∧ (s v) =ᵐ[m] v := by
  let V : Submodule ℂ (X → ℂ) := {
    carrier := {f | Measurable f ∧ MemLp f 2 m}
    zero_mem' := ⟨measurable_const, MemLp.zero⟩
    add_mem' := fun hf hg => ⟨hf.1.add hg.1, hf.2.add hg.2⟩
    smul_mem' := fun z f hf => ⟨hf.1.const_smul z, hf.2.const_smul z⟩ }
  let q : V →ₗ[ℂ] Lp ℂ 2 m := {
    toFun := fun f => f.property.2.toLp f.val
    map_add' := fun f g => MemLp.toLp_add f.property.2 g.property.2
    map_smul' := fun z f => MemLp.toLp_const_smul z f.property.2 }
  have hq : Function.Surjective q := by
    intro v
    let f := (Lp.aestronglyMeasurable v).mk v
    have hfv : (v : X → ℂ) =ᵐ[m] f := (Lp.aestronglyMeasurable v).ae_eq_mk
    have hf : MemLp f 2 m := MemLp.ae_eq hfv (Lp.memLp v)
    refine ⟨⟨f, (Lp.aestronglyMeasurable v).stronglyMeasurable_mk.measurable, hf⟩, ?_⟩
    apply Lp.ext
    exact hf.coeFn_toLp.trans hfv.symm
  obtain ⟨s, hs⟩ := q.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hq)
  refine ⟨V.subtype.comp s, fun v => ⟨(s v).property.1, ?_⟩⟩
  have he : q (s v) = v := DFunLike.congr_fun hs v
  have hae : (s v).val =ᵐ[m] (q (s v) : X → ℂ) := (s v).property.2.coeFn_toLp.symm
  rwa [he] at hae

variable {F : Type u} [Field F] [NumberField F]
  {G P : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] [IsAffine P.X.left]
  [LocallyOfFiniteType G.X.hom]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left]
  {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K)

local notation "A" => AdelicGroupPoints F G
local notation "X" => RationalQuotient F G
local notation "πG" => LeftCosetSpace.mk (rationalSubgroup F G)

/-- The actual ambient weighted integral agrees with the squared integral on the rational
quotient for the pushforward weighted measure. -/
theorem chamberSquareIntegral_eq_automorphic (ell : RealCharacterDual F P → ℝ)
    (hell : Continuous ell) (S : Set (RealCharacterDual F P)) (hS : @MeasurableSet _ (borel _) S)
    {f : X → ℂ} (hf : Measurable f) :
    chamberSquareIntegral hK ell S (f ∘ πG) =
      ∫⁻ x, ‖f x‖ₑ ^ (2 : ℕ) ∂automorphicMeasure F p hK ell (domainHeight F p hK ⁻¹' S) := by
  rw [automorphicMeasure, lintegral_map (hf.enorm.pow_const _) (continuous_toAutomorphic F p).measurable]
  exact (lintegral_domainMeasure_eq_chamberDensity F p hK ell hell S hS
    ((hf.comp (continuous_toAutomorphic F p).measurable).enorm.pow_const _)).symm

/-- The weighted Hilbert space has a linear measurable realization by rational-invariant
functions. Domination of the enlarged quotient measure gives the enlarged chamber norm bound. -/
def WeightedHilbertRealizationStatement : Prop :=
  ∀ (ell : RealCharacterDual F P → ℝ), Continuous ell →
  ∀ (S₀ : Set (RealCharacterDual F P)),
  let T₀ := domainHeight F p hK ⁻¹' S₀
  let ν₀ := automorphicMeasure F p hK ell T₀
  let B := HilbertSpace F p hK ell T₀
  ∃ s : B →ₗ[ℂ] (X → ℂ), ∃ rep : B →ₗ[ℂ] (A → ℂ),
    (∀ v, Measurable (s v) ∧ (s v) =ᵐ[ν₀] v) ∧
    (∀ v, rep v = s v ∘ πG) ∧
    (∀ v, Measurable (rep v)) ∧
    (∀ v (q : rationalSubgroup F G) x, rep v (q.val * x) = rep v x) ∧
    ∀ (S : Set (RealCharacterDual F P)), @MeasurableSet _ (borel _) S →
    ∀ C : ℝ, 0 ≤ C →
    automorphicMeasure F p hK ell (domainHeight F p hK ⁻¹' S) ≤ ENNReal.ofReal C • ν₀ →
    ∀ v, chamberSquareIntegral hK ell S (rep v) < ∞ ∧
      Real.sqrt (chamberSquareIntegral hK ell S (rep v)).toReal ≤ Real.sqrt C * ‖v‖

theorem weightedHilbertRealization : WeightedHilbertRealizationStatement hK := by
  intro ell hell S₀ T₀ ν₀ B
  obtain ⟨s, hs⟩ := exists_measurableLp_section ν₀
  let rep : B →ₗ[ℂ] (A → ℂ) :=
    ((RationalInvariantFunctions F G).subtype.comp (quotientLinearEquiv F G).toLinearMap).comp s
  have hrep (v : B) : rep v = s v ∘ πG := rfl
  refine ⟨s, rep, hs, hrep, fun v => (hs v).1.comp (LeftCosetSpace.measurable_mk _), ?_, ?_⟩
  · intro v q x
    change s v (πG (q.val * x)) = s v (πG x)
    rw [LeftCosetSpace.mk_subgroup_mul]
  intro S hS C hC hdom v
  let ν := automorphicMeasure F p hK ell (domainHeight F p hK ⁻¹' S)
  let I := chamberSquareIntegral hK ell S (rep v)
  have hI : I = ∫⁻ x, ‖s v x‖ₑ ^ (2 : ℕ) ∂ν :=
    chamberSquareIntegral_eq_automorphic hK ell hell S hS (hs v).1
  have hv₀ : MemLp (v : X → ℂ) 2 ν₀ := Lp.memLp v
  have hv : MemLp (s v) 2 ν₀ := MemLp.ae_eq (hs v).2.symm hv₀
  have hv' : MemLp (s v) 2 ν := hv.of_measure_le_smul ENNReal.ofReal_ne_top hdom
  have hfin : I < ∞ := by
    rw [hI]
    have hi := hv'.integrable_enorm_pow (p := 2) (by decide)
    simpa using hasFiniteIntegral_iff_enorm.mp hi.hasFiniteIntegral
  have hn : eLpNorm (s v) 2 ν = I ^ (1 / 2 : ℝ) := by
    rw [hI]
    simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two] using
      eLpNorm_eq_lintegral_rpow_enorm_toReal (p := 2) (by norm_num) (by norm_num)
        hv'.aestronglyMeasurable
  have hcmp := eLpNorm_le_of_measure_le_smul hdom (f := s v) (p := (2 : ℝ≥0∞))
  change eLpNorm (s v) 2 ν ≤ _ at hcmp
  rw [hn, eLpNorm_congr_ae (hs v).2] at hcmp
  have htop : ENNReal.ofReal C ^ (1 / (2 : ℝ≥0∞)).toReal * eLpNorm v 2 ν₀ ≠ ∞ :=
    ENNReal.mul_ne_top (by finiteness) hv₀.eLpNorm_ne_top
  have hr := ENNReal.toReal_mono htop hcmp
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal hC, ← Lp.norm_def] at hr
  have hexp : (1 / (2 : ℝ≥0∞)).toReal = 1 / (2 : ℝ) := by norm_num
  exact ⟨hfin, by simpa only [hexp, ← Real.sqrt_eq_rpow] using hr⟩

end Langlands.Global.WeightedSiegel

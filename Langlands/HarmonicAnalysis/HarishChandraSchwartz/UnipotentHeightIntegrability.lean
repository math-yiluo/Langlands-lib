import Langlands.HarmonicAnalysis.HarishChandraSchwartz.UnipotentHeightVolume
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-! # Integrability of negative powers of the height on dynamic unipotent subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Matrix MeasureTheory
open Langlands.GroupScheme.GeneralLinear
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj NNReal ENNReal

namespace Langlands.HarishChandraSchwartz

section SublevelIntegrability

variable {X : Type*} [MeasurableSpace X]

/-- The sublevel sets `{x | f x ≤ R}` of a weight `f` have `ν`-volume at most `C * R ^ D` for
every real `R ≥ 1`. -/
def HasPolynomialSublevelVolume (ν : Measure X) (f : X → ℝ) (C : ℝ) (D : ℕ) : Prop :=
  ∀ R : ℝ, 1 ≤ R → ν {x | f x ≤ R} ≤ ENNReal.ofReal (C * R ^ D)

/-- **Dyadic integrability.** If `f ≥ 1` is measurable and its sublevel sets have volume
`O(R ^ D)`, then `f ^ (-s)` has finite lower Lebesgue integral for every real `s > D`. -/
theorem HasPolynomialSublevelVolume.lintegral_rpow_neg_lt_top {ν : Measure X} {f : X → ℝ}
    {C : ℝ} {D : ℕ} (hV : HasPolynomialSublevelVolume ν f C D) (hf : Measurable f)
    (hf1 : ∀ x, 1 ≤ f x) {s : ℝ} (hs : (D : ℝ) < s) :
    ∫⁻ x, ENNReal.ofReal (f x ^ (-s)) ∂ν < ⊤ := by
  have hs0 : 0 < s := lt_of_le_of_lt (Nat.cast_nonneg D) hs
  set r : ℝ := (2 : ℝ) ^ (-s) with hr
  have hr0 : 0 ≤ r := Real.rpow_nonneg zero_le_two _
  have h2s : 0 ≤ (2 : ℝ) ^ s := Real.rpow_nonneg zero_le_two _
  let S : ℕ → Set X := fun k => {x | f x ≤ (2 : ℝ) ^ k}
  have hS : ∀ k, MeasurableSet (S k) := fun k => measurableSet_le hf measurable_const
  let g : ℕ → X → ℝ≥0∞ := fun k =>
    (S k).indicator fun _ => ENNReal.ofReal ((2 : ℝ) ^ s) * ENNReal.ofReal r ^ k
  have hpt : ∀ x, ENNReal.ofReal (f x ^ (-s)) ≤ ∑' k, g k x := by
    intro x
    obtain ⟨n, hn₁, hn₂⟩ := exists_nat_pow_near (hf1 x) one_lt_two
    have hmem : x ∈ S (n + 1) := hn₂.le
    refine le_trans ?_ (ENNReal.le_tsum (n + 1))
    change _ ≤ (S (n + 1)).indicator _ x
    rw [Set.indicator_of_mem hmem, ← ENNReal.ofReal_pow hr0, ← ENNReal.ofReal_mul h2s]
    refine ENNReal.ofReal_le_ofReal ?_
    have hle : f x ^ (-s) ≤ ((2 : ℝ) ^ n) ^ (-s) :=
      Real.rpow_le_rpow_of_nonpos (pow_pos two_pos n) hn₁ (neg_nonpos.2 hs0.le)
    have heq : ((2 : ℝ) ^ n) ^ (-s) = (2 : ℝ) ^ s * r ^ (n + 1) := by
      rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul zero_le_two, pow_succ, ← mul_assoc,
        ← Real.rpow_natCast ((2 : ℝ) ^ (-s)), ← Real.rpow_mul zero_le_two, mul_comm (2 ^ s),
        ← Real.rpow_add two_pos, ← Real.rpow_add two_pos]
      congr 1
      ring
    exact hle.trans_eq heq
  have hρ : ENNReal.ofReal r * ENNReal.ofReal ((2 : ℝ) ^ D) < 1 := by
    rw [← ENNReal.ofReal_mul hr0, ENNReal.ofReal_lt_one, hr, ← Real.rpow_natCast,
      ← Real.rpow_add two_pos]
    exact Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  calc ∫⁻ x, ENNReal.ofReal (f x ^ (-s)) ∂ν
      ≤ ∫⁻ x, ∑' k, g k x ∂ν := lintegral_mono hpt
    _ = ∑' k, ∫⁻ x, g k x ∂ν :=
        lintegral_tsum fun k => (measurable_const.indicator (hS k)).aemeasurable
    _ = ∑' k, ENNReal.ofReal ((2 : ℝ) ^ s) * ENNReal.ofReal r ^ k * ν (S k) := by
        congr 1
        funext k
        exact lintegral_indicator_const (hS k) _
    _ ≤ ∑' k, ENNReal.ofReal ((2 : ℝ) ^ s) * ENNReal.ofReal C *
          (ENNReal.ofReal r * ENNReal.ofReal ((2 : ℝ) ^ D)) ^ k := by
        refine ENNReal.tsum_le_tsum fun k => ?_
        have hk : ν (S k) ≤ ENNReal.ofReal C * ENNReal.ofReal ((2 : ℝ) ^ D) ^ k := by
          refine (hV _ (one_le_pow₀ one_le_two)).trans_eq ?_
          rw [ENNReal.ofReal_mul' (pow_nonneg (pow_nonneg zero_le_two _) _),
            ← ENNReal.ofReal_pow (pow_nonneg zero_le_two _), ← pow_mul, ← pow_mul, mul_comm k D]
        calc ENNReal.ofReal ((2 : ℝ) ^ s) * ENNReal.ofReal r ^ k * ν (S k)
            ≤ ENNReal.ofReal ((2 : ℝ) ^ s) * ENNReal.ofReal r ^ k *
                (ENNReal.ofReal C * ENNReal.ofReal ((2 : ℝ) ^ D) ^ k) := by gcongr
          _ = _ := by rw [mul_pow]; ring
    _ = ENNReal.ofReal ((2 : ℝ) ^ s) * ENNReal.ofReal C *
          ∑' k : ℕ, (ENNReal.ofReal r * ENNReal.ofReal ((2 : ℝ) ^ D)) ^ k :=
        ENNReal.tsum_mul_left
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
        (tsum_geometric_lt_top.2 hρ)

/-- If `f ≥ 1` is measurable and its sublevel sets have volume `O(R ^ D)`, then `f ^ (-s)` is
integrable for every real `s > D`. -/
theorem HasPolynomialSublevelVolume.integrable_rpow_neg {ν : Measure X} {f : X → ℝ}
    {C : ℝ} {D : ℕ} (hV : HasPolynomialSublevelVolume ν f C D) (hf : Measurable f)
    (hf1 : ∀ x, 1 ≤ f x) {s : ℝ} (hs : (D : ℝ) < s) :
    Integrable (fun x => f x ^ (-s)) ν := by
  refine ⟨(hf.pow_const (-s)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x =>
    Real.rpow_nonneg (zero_le_one.trans (hf1 x)) _)]
  exact hV.lintegral_rpow_neg_lt_top hf hf1 hs

/-- A function dominated by a multiple of `f ^ (-s)`, `s > D`, is integrable. -/
theorem HasPolynomialSublevelVolume.integrable_of_norm_le {ν : Measure X} {f : X → ℝ}
    {C : ℝ} {D : ℕ} (hV : HasPolynomialSublevelVolume ν f C D) (hf : Measurable f)
    (hf1 : ∀ x, 1 ≤ f x) {s : ℝ} (hs : (D : ℝ) < s) {E : Type*} [NormedAddCommGroup E]
    {φ : X → E} (hφ : AEStronglyMeasurable φ ν) (K : ℝ)
    (hφK : ∀ᵐ x ∂ν, ‖φ x‖ ≤ K * f x ^ (-s)) : Integrable φ ν :=
  ((hV.integrable_rpow_neg hf hf1 hs).const_mul K).mono' hφ hφK

end SublevelIntegrability

end Langlands.HarishChandraSchwartz

namespace Langlands.GroupScheme.MatrixRepresentation

section LocalField

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

local instance heightIntegrabilityTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X
local instance heightIntegrabilityTopologicalGroup : IsTopologicalGroup (rationalPoints G) :=
  rationalPoint_isTopologicalGroup F G

/-- The height `g ↦ ‖g‖_ρ` is continuous on actual rational points. -/
theorem continuous_rationalMatrixNorm {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]
    (ρ : MatrixRepresentation G n) : Continuous (rationalMatrixNorm F ρ) := by
  let := (LocalField.residueNormalizedAbsoluteValue F).toNormedField
  have hinv : ∀ g : rationalPoints G,
      ((ρ.rationalMatrix g)⁻¹ : GL n F) = ρ.rationalMatrix g⁻¹ := fun g => (map_inv _ g).symm
  change Continuous fun g : rationalPoints G =>
    max (HarishChandraSchwartz.entryNorm (ρ.rationalMatrix g : Matrix n n F))
      (HarishChandraSchwartz.entryNorm (((ρ.rationalMatrix g)⁻¹ : GL n F) : Matrix n n F))
  simp_rw [hinv]
  refine Continuous.max ?_ ?_
  · exact HarishChandraSchwartz.continuous_entryNorm_comp fun i j =>
      (Plancherel.continuous_residueNormalizedAbsoluteValue F).comp
        (ρ.continuous_rationalMatrix_entry i j)
  · exact HarishChandraSchwartz.continuous_entryNorm_comp fun i j =>
      (Plancherel.continuous_residueNormalizedAbsoluteValue F).comp
        ((ρ.continuous_rationalMatrix_entry i j).comp continuous_inv)

/-- **Polynomial sublevel volume of the height.** Under the hypotheses of
`exists_measure_rationalMatrixNorm_le_mul_pow`, the height on `H` has polynomial sublevel
volume for `ν`. -/
theorem exists_hasPolynomialSublevelVolume_rationalMatrixNorm
    (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    {N : ℕ} [Nonempty (Fin N)] (ρ₀ : MatrixRepresentation G (Fin N)) (hρ₀ : IsClosedSubgroup ρ₀)
    (H : Subgroup (rationalPoints G)) (hHc : IsClosed (H : Set (rationalPoints G)))
    (hHU : H ≤ (Dynamic.unipotent (CommGroupScheme.groupHom
        (Gm.powerHom (Spec (CommRingCat.of F)) (-1)) ≫ χ)).rationalPoints)
    (hHa : ∀ t : Fˣ, gmRationalPoint t ≫ χ.hom.hom ∈
      Subgroup.normalizer (H : Set (rationalPoints G)))
    [MeasurableSpace H] [BorelSpace H] (ν : Measure H) [ν.IsHaarMeasure] [ν.Regular] :
    ∃ (C : ℝ) (D : ℕ), HarishChandraSchwartz.HasPolynomialSublevelVolume ν
      (fun x : H => rationalMatrixNorm F ρ₀ x) C D :=
  exists_measure_rationalMatrixNorm_le_mul_pow F χ ρ₀ hρ₀ H hHc hHU hHa ν

/-- **Integrability of negative powers of the height.** Let `χ` be a cocharacter of an affine
group `G` of finite type over a non-archimedean local field `F`, `ρ₀` a closed representation,
and `H` a closed subgroup of `Ū(F) = U(χ⁻¹)(F)` normalized by every `χ(t)`. For every regular
Haar measure `ν` on `H` there is `D` such that `x ↦ ‖x‖_ρ₀ ^ (-s)` is `ν`-integrable for every
real `s > D`. -/
theorem exists_integrable_rationalMatrixNorm_rpow_neg
    (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    {N : ℕ} [Nonempty (Fin N)] (ρ₀ : MatrixRepresentation G (Fin N)) (hρ₀ : IsClosedSubgroup ρ₀)
    (H : Subgroup (rationalPoints G)) (hHc : IsClosed (H : Set (rationalPoints G)))
    (hHU : H ≤ (Dynamic.unipotent (CommGroupScheme.groupHom
        (Gm.powerHom (Spec (CommRingCat.of F)) (-1)) ≫ χ)).rationalPoints)
    (hHa : ∀ t : Fˣ, gmRationalPoint t ≫ χ.hom.hom ∈
      Subgroup.normalizer (H : Set (rationalPoints G)))
    [MeasurableSpace H] [BorelSpace H] (ν : Measure H) [ν.IsHaarMeasure] [ν.Regular] :
    ∃ D : ℕ, ∀ s : ℝ, (D : ℝ) < s →
      Integrable (fun x : H => rationalMatrixNorm F ρ₀ x ^ (-s)) ν := by
  obtain ⟨C, D, hV⟩ :=
    exists_hasPolynomialSublevelVolume_rationalMatrixNorm F χ ρ₀ hρ₀ H hHc hHU hHa ν
  refine ⟨D, fun s hs => hV.integrable_rpow_neg ?_ (fun x => one_le_rationalMatrixNorm F ρ₀ x) hs⟩
  exact ((continuous_rationalMatrixNorm F ρ₀).comp continuous_subtype_val).measurable

end LocalField

end Langlands.GroupScheme.MatrixRepresentation

import Langlands.Representation.Character.CompactCoefficientPairing
import Langlands.Representation.Character.CompactTypeAdmissibility
import Langlands.HarmonicAnalysis.Distribution.SmoothedPushforwardEvaluation
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.RepresentationTheory.Character

/-! # Compact interaction detected by a smoothed slice pairing -/

noncomputable section

namespace Langlands.Character

open Function HarmonicAnalysis MeasureTheory MeasureTheory.Measure
open Hecke.TestFunction (leftTranslate leftTranslate_apply)

variable {G M X Y : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
  [Group M] [TopologicalSpace M]

/-- The restriction to the subgroup of `M` carried by `i` into `K`, with values in `K`. -/
def compactSliceRestriction (K : OpenSubgroup G) (i : M →* G) (hi : Continuous i) :
    K.comap i hi →* K :=
  (i.comp (K.comap i hi).toSubgroup.subtype).codRestrict K.toSubgroup Subtype.property

private theorem exists_traceTranslateCoefficient [FiniteDimensional ℂ X]
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (τ : Representation ℂ K X)
    (hτ : IsSmooth τ) (D : Distribution G) (g : G) :
    ∃ a : Module.Dual ℂ (Module.End ℂ X), ∀ k : K,
      D (compactTraceCosetTest K hK τ hτ (g * k.val)) = a (τ k⁻¹) := by
  let : IsTopologicalGroup K := inferInstanceAs (IsTopologicalGroup K.toSubgroup)
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let Q := Representation.linHom (Representation.trivial ℂ K X) τ
  obtain ⟨N, _, hN⟩ :=
    Renard.CompactRepresentation.exists_openNormal_trivial_of_finiteDimensional τ hτ
  have hfix (k : K) (hk : k ∈ N) (T : Module.End ℂ X) : Q k T = T := by
    apply LinearMap.ext
    intro x
    change τ k (T x) = T x
    exact hN k hk _
  have hQ : IsSmooth Q := fun T => ⟨N, fun k => hfix k.val k.property T⟩
  let tr := LinearMap.trace ℂ X
  have htr : IsSmoothVector Q.dual tr := ⟨N, fun k => LinearMap.ext fun T => by
    change tr (Q k.val⁻¹ T) = tr T
    rw [hfix _ (N.inv_mem k.property)]⟩
  let w := CompactCoefficientSemisimplicity.coefficientTest Q hQ
    (fun _ _ _ => HasCompactSupport.of_compactSpace _) htr
  let a := D.comp ((leftTranslate g).toLinearMap.comp ((SchwartzBruhat.extendZero K.isOpen).comp w))
  refine ⟨a, fun k => ?_⟩
  change D (leftTranslate (g * k.val) (SchwartzBruhat.extendZero K.isOpen (compactTraceTest τ hτ))) =
    D (leftTranslate g (SchwartzBruhat.extendZero K.isOpen (w (τ k⁻¹))))
  congr 1
  apply Hecke.TestFunction.ext
  intro x
  simp only [leftTranslate_apply, mul_inv_rev, mul_assoc]
  by_cases hx : g⁻¹ * x ∈ K
  · let s : K := ⟨g⁻¹ * x, hx⟩
    change SchwartzBruhat.extendZero K.isOpen (compactTraceTest τ hτ) ((k⁻¹ * s : K) : G) =
      SchwartzBruhat.extendZero K.isOpen (w (τ k⁻¹)) (s : G)
    rw [SchwartzBruhat.extendZero_apply_subtype, SchwartzBruhat.extendZero_apply_subtype,
      compactTraceTest_apply, map_mul]
    change tr (τ k⁻¹ * τ s) = tr (τ s * τ k⁻¹)
    exact LinearMap.trace_mul_comm ℂ _ _
  · have hx' : (k.val : G)⁻¹ * (g⁻¹ * x) ∉ K := by
      change (k.val : G)⁻¹ * (g⁻¹ * x) ∉ K.toSubgroup
      rwa [K.toSubgroup.mul_mem_cancel_left (K.inv_mem k.property)]
    rw [SchwartzBruhat.extendZero_apply_of_not_mem K.isOpen _ hx',
      SchwartzBruhat.extendZero_apply_of_not_mem K.isOpen _ hx]

/-- A nonzero pairing of a slice trace with a smoothed ambient distribution
detects an intertwiner on the intersection and a nonzero translated trace test. -/
def CompactTraceDescentPairingStatement [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [IsTopologicalGroup M] [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    [FiniteDimensional ℂ X] [FiniteDimensional ℂ Y]
    (μ : Measure M) [μ.IsHaarMeasure]
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (τ : Representation ℂ K X)
    (hτ : IsSmooth τ) (σ : Representation ℂ M Y) (D : Distribution G)
    (i : M →* G) (hi : Continuous i) (y : G) : Prop :=
  IsSmooth σ →
  let Φ (m : M) := D (compactTraceCosetTest K hK τ hτ (y * i m))
  (∫ m, σ.character m * Φ m ∂μ) ≠ 0 →
  let J := K.comap i hi
  (∃ T : Representation.IntertwiningMap (τ.comp (compactSliceRestriction K i hi))
    (σ.comp J.toSubgroup.subtype), T ≠ 0) ∧ ∃ m, Φ m ≠ 0

variable [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
  [IsTopologicalGroup M] [T2Space M] [CompactSpace M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]
  [FiniteDimensional ℂ X] [FiniteDimensional ℂ Y]

theorem compactTraceDescentPairing (μ : Measure M) [μ.IsHaarMeasure]
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (τ : Representation ℂ K X)
    (hτ : IsSmooth τ) (σ : Representation ℂ M Y) (D : Distribution G)
    (i : M →* G) (hi : Continuous i) (y : G) :
    CompactTraceDescentPairingStatement μ K hK τ hτ σ D i hi y := by
  intro hσ
  dsimp only
  intro hNZ
  let : IsTopologicalGroup K := inferInstanceAs (IsTopologicalGroup K.toSubgroup)
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let J := K.comap i hi
  let : IsTopologicalGroup J := inferInstanceAs (IsTopologicalGroup J.toSubgroup)
  let : CompactSpace J := isCompact_iff_compactSpace.mp (J.isClosed.isCompact)
  let j := compactSliceRestriction K i hi
  let A := τ.comp j
  let B := σ.comp J.toSubgroup.subtype
  let Φ (m : M) := D (compactTraceCosetTest K hK τ hτ (y * i m))
  let F (m : M) := σ.character m * Φ m
  change (∫ m, F m ∂μ) ≠ 0 at hNZ
  refine ⟨?_, ?_⟩
  · by_contra! hHom
    let ν := μ.comap J.toSubgroup.subtype
    let : ν.IsHaarMeasure := IsHaarMeasure.comap (mH := inferInstance) μ J.isOpen.isOpenEmbedding_subtypeVal
    let : μ.IsMulRightInvariant := CompactFactorization.isMulRightInvariant_of_compactSpace μ
    have hA := isSmooth_comp j ((hi.comp continuous_subtype_val).subtype_mk _) hτ
    have hB := isSmooth_comp J.toSubgroup.subtype continuous_subtype_val hσ
    have hInner (m : M) : (∫ k : J, F (m * (k.val : M)) ∂ν) = 0 := by
      obtain ⟨a, ha⟩ := exists_traceTranslateCoefficient K hK τ hτ D (y * i m)
      let b := (LinearMap.trace ℂ Y).comp (LinearMap.mulLeft ℂ (σ m))
      have h₀ := Representation.Character.compactCoefficientPairing ν A B hA hB hHom a b
      rw [← h₀]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun k => by
        have hΦ : Φ (m * k.val) = a (τ ((j k)⁻¹)) := by
          change D (compactTraceCosetTest K hK τ hτ (y * i (m * k.val))) = _
          rw [map_mul, ← mul_assoc]
          exact ha (j k)
        change σ.character (m * k.val) * Φ (m * k.val) = a (τ (j k⁻¹)) * b (σ k.val)
        rw [hΦ, ← map_inv j, mul_comm]
        congr 1
        change LinearMap.trace ℂ Y (σ (m * k.val)) =
          LinearMap.trace ℂ Y (σ m * σ k.val)
        rw [map_mul]
    let test := SchwartzBruhat.extendZero K.isOpen (compactTraceTest τ hτ)
    have hΦc : Continuous Φ :=
      ((Distribution.isLocallyConstant_eval_leftTranslate D test).comp_continuous
        (continuous_const.mul hi)).continuous
    have hχ : Continuous σ.character := by
      apply (compactTraceTest σ hσ).continuous.congr
      exact fun m => compactTraceTest_apply σ hσ m
    have hcont : Continuous F := hχ.mul hΦc
    have hInt : Integrable (fun p : M × J => F (p.1 * p.2.val)) (μ.prod ν) :=
      Continuous.integrable_of_hasCompactSupport
        (hcont.comp (continuous_fst.mul (continuous_subtype_val.comp continuous_snd)))
        (HasCompactSupport.of_compactSpace _)
    have hSwap := integral_integral_swap (f := fun m (k : J) => F (m * k.val)) hInt
    simp_rw [hInner, integral_zero, integral_mul_right_eq_self] at hSwap
    rw [integral_const, Complex.real_smul] at hSwap
    have hν : 0 < ν.real Set.univ := ENNReal.toReal_pos
      (isOpen_univ.measure_pos ν Set.univ_nonempty).ne' isCompact_univ.measure_lt_top.ne
    exact (mul_ne_zero (Complex.ofReal_ne_zero.mpr hν.ne') hNZ) hSwap.symm
  · by_contra! hAll
    exact hNZ (by simp [F, Φ, hAll])

end Langlands.Character

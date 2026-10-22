import Langlands.Automorphic.Smooth

/-! # Reconstructing finite-level adelic functions from actual smooth slices -/

noncomputable section
universe u

namespace Langlands.Automorphic

open Langlands.Global NumberField ContinuousRationalFunctions

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- Evaluate an actual family of smooth infinite slices on an adelic matrix. -/
def evaluateSmoothSlices
    (F : FiniteAdelicGL K n → ArchimedeanGL.SmoothFunctions K n)
    (x : AdelicGL K n) : ℂ :=
  (F (AdelicGL.finite K n x)).val (AdelicGL.infinite K n x)

@[simp]
theorem evaluateSmoothSlices_pair
    (F : FiniteAdelicGL K n → ArchimedeanGL.SmoothFunctions K n)
    (a : InfiniteAdelicGL K n) (b : FiniteAdelicGL K n) :
    evaluateSmoothSlices K n F (AdelicGL.pair K n a b) = (F b).val a := by
  simp [evaluateSmoothSlices]

/-- One open right stabilizer for the full family gives joint adelic continuity. -/
theorem continuous_evaluateSmoothSlices
    (F : FiniteAdelicGL K n → ArchimedeanGL.SmoothFunctions K n)
    (L : OpenSubgroup (FiniteAdelicGL K n))
    (hL : ∀ (b : FiniteAdelicGL K n) (l : L), F (b * l.val) = F b) :
    Continuous (evaluateSmoothSlices K n F) := by
  rw [continuous_iff_continuousAt]
  intro x
  let b := AdelicGL.finite K n x
  have ho : IsOpen {y : AdelicGL K n | b⁻¹ * AdelicGL.finite K n y ∈ L} :=
    L.isOpen.preimage (continuous_const.mul (AdelicGL.finite K n).continuous)
  have hx : x ∈ {y : AdelicGL K n | b⁻¹ * AdelicGL.finite K n y ∈ L} := by
    change b⁻¹ * b ∈ L
    simp
  have hc := ((ArchimedeanGL.continuous K n (F b)).comp
    (AdelicGL.infinite K n).continuous).continuousAt (x := x)
  apply hc.congr
  filter_upwards [ho.mem_nhds hx] with y hy
  have h := hL b ⟨b⁻¹ * AdelicGL.finite K n y, hy⟩
  simp only [mul_inv_cancel_left] at h
  change (F b).val _ = (F (AdelicGL.finite K n y)).val _
  rw [h]
  rfl

/-- Smooth slices obeying rational covariance and one specified open finite level. -/
def finiteLevelSmoothSliceFamilies (L : OpenSubgroup (FiniteAdelicGL K n)) :
    Submodule ℂ (FiniteAdelicGL K n → ArchimedeanGL.SmoothFunctions K n) where
  carrier := {F |
    (∀ (b : FiniteAdelicGL K n) (l : L), F (b * l.val) = F b) ∧
    ∀ (γ : RationalGL K n) (b : FiniteAdelicGL K n) (a : InfiniteAdelicGL K n),
      (F (AdelicGL.finite K n (AdelicGL.rational K n γ) * b)).val
        (AdelicGL.infinite K n (AdelicGL.rational K n γ) * a) = (F b).val a}
  zero_mem' := by constructor <;> intros <;> rfl
  add_mem' {F G} hF hG := by
    constructor
    · intro b l
      change F (b * l.val) + G (b * l.val) = F b + G b
      rw [hF.1 b l, hG.1 b l]
    · intro γ b a
      change
        (F (AdelicGL.finite K n (AdelicGL.rational K n γ) * b)).val
          (AdelicGL.infinite K n (AdelicGL.rational K n γ) * a) +
        (G (AdelicGL.finite K n (AdelicGL.rational K n γ) * b)).val
          (AdelicGL.infinite K n (AdelicGL.rational K n γ) * a) =
        (F b).val a + (G b).val a
      rw [hF.2 γ b a, hG.2 γ b a]
  smul_mem' c F hF := by
    constructor
    · intro b l
      change c • F (b * l.val) = c • F b
      rw [hF.1 b l]
    · intro γ b a
      change c •
        (F (AdelicGL.finite K n (AdelicGL.rational K n γ) * b)).val
          (AdelicGL.infinite K n (AdelicGL.rational K n γ) * a) =
        c • (F b).val a
      rw [hF.2 γ b a]

abbrev FiniteLevelSmoothSliceFamilies (L : OpenSubgroup (FiniteAdelicGL K n)) :=
  finiteLevelSmoothSliceFamilies K n L

/-- The reconstruction is an actual continuous rational-invariant function. -/
def reconstructContinuousSlices (L : OpenSubgroup (FiniteAdelicGL K n)) :
    FiniteLevelSmoothSliceFamilies K n L →ₗ[ℂ] ContinuousRationalFunctions K n where
  toFun F := ⟨⟨evaluateSmoothSlices K n F.val, by
    intro γ x
    change evaluateSmoothSlices K n F.val (AdelicGL.rational K n γ * x) =
      evaluateSmoothSlices K n F.val x
    simpa only [evaluateSmoothSlices, map_mul] using
      F.property.2 γ (AdelicGL.finite K n x) (AdelicGL.infinite K n x)⟩,
    continuous_evaluateSmoothSlices K n F.val L F.property.1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem evaluate_reconstructContinuousSlices (L : OpenSubgroup (FiniteAdelicGL K n))
    (F : FiniteLevelSmoothSliceFamilies K n L) (x : AdelicGL K n) :
    evaluate K n (reconstructContinuousSlices K n L F) x =
      evaluateSmoothSlices K n F.val x := rfl

/-- Reconstruction retains real smoothness and the same open finite stabilizer. -/
def reconstructFiniteSmoothSlices (L : OpenSubgroup (FiniteAdelicGL K n)) :
    FiniteLevelSmoothSliceFamilies K n L →ₗ[ℂ] FiniteSmoothRationalFunctions K n where
  toFun F := ⟨reconstructContinuousSlices K n L F, by
    constructor
    · change reconstructContinuousSlices K n L F ∈
        (⨅ b : FiniteAdelicGL K n,
          (ArchimedeanGL.smoothFunctions K n).comap (infiniteSlice K n b))
      apply (Submodule.mem_iInf _).mpr
      intro b
      have heq : infiniteSlice K n b (reconstructContinuousSlices K n L F) = (F.val b).val := by
        funext a
        exact evaluateSmoothSlices_pair K n F.val a b
      change infiniteSlice K n b (reconstructContinuousSlices K n L F) ∈
        ArchimedeanGL.smoothFunctions K n
      rw [heq]
      exact (F.val b).property
    · refine ⟨L, ?_⟩
      intro l
      apply Subtype.ext
      apply Subtype.ext
      funext x
      change evaluateSmoothSlices K n F.val (x * AdelicGL.ofFinite K n l.val) =
        evaluateSmoothSlices K n F.val x
      simp only [evaluateSmoothSlices, map_mul, AdelicGL.ofFinite_eq_pair,
        AdelicGL.finite_pair, AdelicGL.infinite_pair, mul_one]
      rw [F.property.1 _ l]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem evaluate_reconstructFiniteSmoothSlices (L : OpenSubgroup (FiniteAdelicGL K n))
    (F : FiniteLevelSmoothSliceFamilies K n L)
    (a : InfiniteAdelicGL K n) (b : FiniteAdelicGL K n) :
    evaluate K n (reconstructFiniteSmoothSlices K n L F).val (AdelicGL.pair K n a b) =
      (F.val b).val a := evaluateSmoothSlices_pair K n F.val a b

theorem reconstructFiniteSmoothSlices_injective (L : OpenSubgroup (FiniteAdelicGL K n)) :
    Function.Injective (reconstructFiniteSmoothSlices K n L) := by
  intro F G h
  apply Subtype.ext
  funext b
  apply Subtype.ext
  funext a
  simpa only [evaluate_reconstructFiniteSmoothSlices] using
    congrArg (fun f : FiniteSmoothRationalFunctions K n =>
      evaluate K n f.val (AdelicGL.pair K n a b)) h

end Langlands.Automorphic

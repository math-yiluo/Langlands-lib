import Langlands.GroupScheme.Examples.SU3RootJumpParity

/-! # Positive rescaling of coordinate valuations and jumps -/

noncomputable section

universe u

namespace Langlands.GroupScheme.SU3Root

/-- Multiplication of finite real values by a scalar, preserving infinity. -/
def scaleTop (a : ℝ) : WithTop ℝ →+ WithTop ℝ where
  toFun := WithTop.map (a * ·)
  map_zero' := by simp
  map_add' := by
    intro x y
    induction x with
    | top => simp
    | coe x =>
      induction y with
      | top => simp
      | coe y =>
        change ((a * (x + y) : ℝ) : WithTop ℝ) =
          ((a * x : ℝ) : WithTop ℝ) + ((a * y : ℝ) : WithTop ℝ)
        rw [← WithTop.coe_add, mul_add]

@[simp] theorem scaleTop_top (a : ℝ) : scaleTop a ⊤ = ⊤ := rfl

@[simp] theorem scaleTop_coe (a r : ℝ) :
    scaleTop a (r : WithTop ℝ) = ((a * r : ℝ) : WithTop ℝ) := rfl

theorem scaleTop_strictMono {a : ℝ} (ha : 0 < a) : StrictMono (scaleTop a) := by
  intro x y h
  induction y with
  | top =>
    induction x with
    | top => exact (lt_irrefl _ h).elim
    | coe x => exact WithTop.coe_lt_top _
  | coe y =>
    induction x with
    | top => exact (not_top_lt h).elim
    | coe x =>
      exact WithTop.coe_lt_coe.mpr (mul_lt_mul_of_pos_left (WithTop.coe_lt_coe.mp h) ha)

/-- Positive rescaling of an additive valuation into extended real values. -/
def rescaleValuation {L : Type u} [Field L] (ω : AddValuation L (WithTop ℝ))
    (a : ℝ) (ha : 0 < a) : AddValuation L (WithTop ℝ) :=
  ω.map ⟨scaleTop a, (scaleTop_strictMono ha).monotone⟩ rfl

@[simp] theorem rescaleValuation_apply {L : Type u} [Field L]
    (ω : AddValuation L (WithTop ℝ)) (a : ℝ) (ha : 0 < a) (x : L) :
    rescaleValuation ω a ha x = scaleTop a (ω x) := rfl

theorem halfTop_scaleTop (a : ℝ) (x : WithTop ℝ) :
    halfTop (scaleTop a x) = scaleTop a (halfTop x) := by
  induction x with
  | top => rfl
  | coe x =>
    rw [scaleTop_coe, halfTop_coe, halfTop_coe, scaleTop_coe]
    congr 1
    ring

namespace Parameters

variable {L : Type u} [Field L] {c : RingInvolution L}
  (ω : AddValuation L (WithTop ℝ)) (a : ℝ) (ha : 0 < a)

theorem depthA_rescale (p : Parameters c) :
    depthA (rescaleValuation ω a ha) p = scaleTop a (depthA ω p) :=
  halfTop_scaleTop a (ω p.second)

theorem depthDouble_rescale (z : central c) :
    depthDouble (rescaleValuation ω a ha) z = scaleTop a (depthDouble ω z) := rfl

theorem mem_quotientJumpValues_rescale_iff (r : ℝ) :
    a * r ∈ quotientJumpValues (c := c) (rescaleValuation ω a ha) ↔
      r ∈ quotientJumpValues (c := c) ω := by
  simp only [quotientJumpValues, Set.mem_ofPred_eq, depthA_rescale,
    ← scaleTop_coe a r, (scaleTop_strictMono ha).le_iff_le,
    (scaleTop_strictMono ha).lt_iff_lt]

theorem mem_centralJumpValues_rescale_iff (r : ℝ) :
    a * r ∈ centralJumpValues (c := c) (rescaleValuation ω a ha) ↔
      r ∈ centralJumpValues (c := c) ω := by
  simp only [centralJumpValues, Set.mem_ofPred_eq, depthDouble_rescale,
    ← scaleTop_coe a r, (scaleTop_strictMono ha).le_iff_le,
    (scaleTop_strictMono ha).lt_iff_lt]

/-- Positive changes of normalization preserve existence of an indivisible
central coordinate jump. -/
theorem hasIndivisibleCentralJump_rescale_iff :
    HasIndivisibleCentralJump (c := c) (rescaleValuation ω a ha) ↔
      HasIndivisibleCentralJump (c := c) ω := by
  constructor
  · rintro ⟨r, hr, hq⟩
    have heq : a * (r / a) = r := mul_div_cancel₀ r (ne_of_gt ha)
    have hhalf : a * ((r / a) / 2) = r / 2 := by rw [← mul_div_assoc, heq]
    refine ⟨r / a, ?_, ?_⟩
    · exact (mem_centralJumpValues_rescale_iff ω a ha (r / a)).mp (by rwa [heq])
    · intro hq'
      apply hq
      rw [← hhalf]
      exact (mem_quotientJumpValues_rescale_iff ω a ha _).mpr hq'
  · rintro ⟨r, hr, hq⟩
    refine ⟨a * r, (mem_centralJumpValues_rescale_iff ω a ha r).mpr hr, ?_⟩
    intro hq'
    apply hq
    apply (mem_quotientJumpValues_rescale_iff ω a ha (r / 2)).mp
    simpa only [mul_div_assoc] using hq'

end Parameters

end Langlands.GroupScheme.SU3Root

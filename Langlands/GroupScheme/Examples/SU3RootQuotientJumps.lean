import Langlands.GroupScheme.Examples.SU3RootQuotientDepth
import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-! # Quadratic root-coordinate jumps modulo the central subgroup -/

noncomputable section

open scoped Pointwise

namespace Langlands.GroupScheme.SU3Root.Parameters

universe u
variable {L : Type u} [Field L] {c : RingInvolution L}

/-- The ordinary-root jump condition on the literal coordinate group. -/
def quotientJumpValues (ω : AddValuation L (WithTop ℝ)) : Set ℝ :=
  {r | ¬ {p : Parameters c | (r : WithTop ℝ) ≤ depthA ω p} ⊆
    {p : Parameters c | (r : WithTop ℝ) < depthA ω p} *
      (central c : Set (Parameters c))}

/-- The depth jump condition on the literal zero-first-coordinate subgroup. -/
def centralJumpValues (ω : AddValuation L (WithTop ℝ)) : Set ℝ :=
  {r | ¬ {z : central c | (r : WithTop ℝ) ≤ depthDouble ω z} ⊆
    {z : central c | (r : WithTop ℝ) < depthDouble ω z}}

/-- Two parameters differ by right multiplication by a central point exactly when
 their first coordinates agree. -/
theorem exists_central_mul_eq_iff (p q : Parameters c) :
    (∃ z : central c, p * z.val = q) ↔ p.first = q.first := by
  constructor
  · rintro ⟨z, rfl⟩
    simp only [first_mul, (mem_central z.val).mp z.property, add_zero]
  · intro h
    refine ⟨⟨p⁻¹ * q, ?_⟩, by simp⟩
    simp only [mem_central, first_mul, first_inv, ← h, neg_add_cancel]

/-- Every central point belongs to the product of any strict ball with the central
 subgroup, since the identity has infinite depth. -/
theorem mem_strict_mul_central_of_first_eq_zero
    (ω : AddValuation L (WithTop ℝ)) (r : ℝ) (p : Parameters c)
    (hp : p.first = 0) :
    p ∈ {q : Parameters c | (r : WithTop ℝ) < depthA ω q} *
      (central c : Set (Parameters c)) := by
  refine Set.mem_mul.mpr ⟨1, ?_, p, hp, one_mul p⟩
  simp [depthA]

/-- The optimal trace-one representative detects strict-ball membership modulo
 the actual central subgroup. -/
theorem mem_strict_mul_central_iff
    (ω : AddValuation L (WithTop ℝ))
    {t : L} (ht : t + c.bar t = 1)
    (hmax : ∀ y : L, y + c.bar y = 1 → ω y ≤ ω t)
    (r : ℝ) (p : Parameters c) (hp : p.first ≠ 0) :
    p ∈ {q : Parameters c | (r : WithTop ℝ) < depthA ω q} *
      (central c : Set (Parameters c)) ↔
      (r : WithTop ℝ) < depthA ω (liftOfTraceOne ht p.first) := by
  constructor
  · rintro h
    obtain ⟨q, hq, z, hz, hqz⟩ := Set.mem_mul.mp h
    have hfirst : q.first = p.first :=
      (exists_central_mul_eq_iff q p).mp ⟨⟨z, hz⟩, hqz⟩
    have hbound := depthA_le_liftOfTraceOne ω ht hmax q (by rwa [hfirst])
    rw [hfirst] at hbound
    exact hq.trans_le hbound
  · intro h
    obtain ⟨z, hz⟩ := (exists_central_mul_eq_iff
      (liftOfTraceOne ht p.first) p).mpr (liftOfTraceOne_first ht p.first)
    exact Set.mem_mul.mpr ⟨_, h, z.val, z.property, hz⟩

/-- Quotient jumps are exactly the finite optimal depths of nonzero first
 coordinates. No discreteness assumption is needed for this equivalence. -/
theorem mem_quotientJumpValues_iff
    (ω : AddValuation L (WithTop ℝ))
    (hinv : ∀ y : L, ω (c.bar y) = ω y)
    {t : L} (ht : t + c.bar t = 1)
    (hmax : ∀ y : L, y + c.bar y = 1 → ω y ≤ ω t)
    (r : ℝ) :
    r ∈ quotientJumpValues (c := c) ω ↔
      ∃ x : L, x ≠ 0 ∧ ω x + halfTop (ω t) = (r : WithTop ℝ) := by
  constructor
  · intro h
    obtain ⟨p, hp, hnot⟩ := Set.not_subset.mp h
    have hp0 : p.first ≠ 0 := fun h0 =>
      hnot (mem_strict_mul_central_of_first_eq_zero ω r p h0)
    have hle := hp.trans (depthA_le_liftOfTraceOne ω ht hmax p hp0)
    have hge : depthA ω (liftOfTraceOne ht p.first) ≤ (r : WithTop ℝ) :=
      le_of_not_gt (fun hlt => hnot ((mem_strict_mul_central_iff ω ht hmax r p hp0).mpr hlt))
    refine ⟨p.first, hp0, ?_⟩
    rw [← depthA_liftOfTraceOne ω hinv ht]
    exact le_antisymm hge hle
  · rintro ⟨x, hx, hdepth⟩
    refine Set.not_subset.mpr ⟨liftOfTraceOne ht x, ?_, ?_⟩
    · change (r : WithTop ℝ) ≤ depthA ω (liftOfTraceOne ht x)
      rw [depthA_liftOfTraceOne ω hinv ht, hdepth]
    · intro h
      have hlt := (mem_strict_mul_central_iff ω ht hmax r
        (liftOfTraceOne ht x) (by simpa using hx)).mp h
      simp only [liftOfTraceOne_first, depthA_liftOfTraceOne ω hinv ht,
        hdepth, lt_self_iff_false] at hlt

/-- Central jumps are exactly the finite depths attained by nonidentity central
 points. -/
theorem mem_centralJumpValues_iff
    (ω : AddValuation L (WithTop ℝ)) (r : ℝ) :
    r ∈ centralJumpValues (c := c) ω ↔
      ∃ z : central c, z ≠ 1 ∧ depthDouble ω z = (r : WithTop ℝ) := by
  constructor
  · intro h
    obtain ⟨z, hz, hnot⟩ := Set.not_subset.mp h
    have heq : depthDouble ω z = (r : WithTop ℝ) :=
      le_antisymm (le_of_not_gt hnot) hz
    refine ⟨z, ?_, heq⟩
    intro hz1
    have htop := (depthDouble_eq_top_iff ω z).mpr hz1
    exact WithTop.coe_ne_top (heq.symm.trans htop)
  · rintro ⟨z, _, hz⟩
    refine Set.not_subset.mpr ⟨z, ?_, ?_⟩ <;>
      simp only [Set.mem_ofPred_eq, hz, le_refl, lt_self_iff_false, not_false_eq_true]

end Langlands.GroupScheme.SU3Root.Parameters

import Langlands.LinearAlgebra.CartanE6RootCoordinates

/-! # Relative-root restrictions with unmarked short arm in type E6 -/

noncomputable section

open scoped BigOperators

namespace Langlands.CartanE6Root

/-- A marking stable under opposition with the short-arm end unmarked. The
possibly nontrivial star action exchanges the two equal arms. -/
structure BranchMarking where
  swapsArms : Bool
  endsMarked : Bool
  innerArmMarked : Bool
  centralMarked : Bool
  deriving DecidableEq

namespace BranchMarking

abbrev Coordinates := Fin 6 → ℤ

/-- The chosen representative vertices of the marked star orbits. -/
def active (p : BranchMarking) : Fin 6 → Bool :=
  ![p.endsMarked, false, p.innerArmMarked, p.centralMarked,
    p.innerArmMarked && !p.swapsArms, p.endsMarked && !p.swapsArms]

/-- Restriction discards unmarked vertices and adds coordinates on a marked
star orbit at its chosen representative. -/
def project (p : BranchMarking) (c : Coordinates) : Coordinates :=
  ![if p.endsMarked then c 0 + (if p.swapsArms then c 5 else 0) else 0,
    0,
    if p.innerArmMarked then c 2 + (if p.swapsArms then c 4 else 0) else 0,
    if p.centralMarked then c 3 else 0,
    if p.innerArmMarked && !p.swapsArms then c 4 else 0,
    if p.endsMarked && !p.swapsArms then c 5 else 0]

abbrev unit (i : Fin 6) : Coordinates := Pi.single i 1

/-- Projected signed E6 roots, including the zero restrictions. -/
def IsProjectedRoot (p : BranchMarking) (c : Coordinates) : Prop :=
  ∃ (s : Bool) (i : Fin 36),
    (if s then -(p.project (positiveCoefficients i)) else p.project (positiveCoefficients i)) = c

instance (p : BranchMarking) (c : Coordinates) : Decidable (p.IsProjectedRoot c) :=
  inferInstanceAs (Decidable (∃ (_ : Bool) (_ : Fin 36), _))

theorem project_apply_eq_zero_of_inactive (p : BranchMarking) (c : Coordinates)
    (i : Fin 6) (h : p.active i = false) : p.project c i = 0 := by
  obtain ⟨s, a, b, d⟩ := p
  cases s <;> cases a <;> cases b <;> cases d <;> fin_cases i <;>
    simp [project, active] at h ⊢

theorem IsProjectedRoot.apply_eq_zero_of_inactive {p : BranchMarking} {c : Coordinates}
    (hc : p.IsProjectedRoot c) (i : Fin 6) (h : p.active i = false) : c i = 0 := by
  obtain ⟨s, j, rfl⟩ := hc
  cases s <;> simp [p.project_apply_eq_zero_of_inactive _ i h]

/-- The necessary crystallographic reflection condition on a projection. A
projected root supported on one coordinate gives an integral pairing with each
marked orbit, and its reflection preserves the projections of all roots. -/
def HasIntegralReflections (p : BranchMarking) : Prop :=
  ∀ (i : Fin 6) (m : ℤ), p.active i = true → 0 < m → p.IsProjectedRoot (m • unit i) →
    ∃ f : Coordinates, m * f i = 2 ∧
      ∀ c : Coordinates, p.IsProjectedRoot c →
        p.IsProjectedRoot (c - (m * ∑ j : Fin 6, c j * f j) • unit i)

private structure ReflectionTest where
  pivot : Fin 6
  multiple : ℤ
  upper : Coordinates
  witness : Coordinates

private def test : BranchMarking → ReflectionTest
  | ⟨false, false, false, true⟩ =>
    ⟨3, 3, ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]⟩
  | ⟨false, false, true, false⟩ =>
    ⟨2, 1, ![0, 0, 0, 0, 2, 0], ![0, 0, 1, 0, 2, 0]⟩
  | ⟨false, false, true, true⟩ =>
    ⟨2, 1, ![0, 0, 0, 1, 0, 0], ![0, 0, 2, 2, 1, 0]⟩
  | ⟨false, true, false, true⟩ =>
    ⟨0, 1, ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 2, 0, 0]⟩
  | ⟨false, true, true, false⟩ =>
    ⟨2, 1, ![1, 0, 0, 0, 1, 0], ![1, 0, 2, 0, 1, 0]⟩
  | ⟨false, true, true, true⟩ =>
    ⟨3, 1, ![0, 0, 1, 0, 1, 0], ![0, 0, 1, 2, 1, 0]⟩
  | ⟨true, false, false, true⟩ =>
    ⟨3, 3, ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]⟩
  | ⟨true, false, true, false⟩ =>
    ⟨2, 3, ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]⟩
  | ⟨true, false, true, true⟩ =>
    ⟨2, 1, ![0, 0, 0, 2, 0, 0], ![0, 0, 3, 2, 0, 0]⟩
  | ⟨true, true, false, true⟩ =>
    ⟨0, 1, ![0, 0, 0, 2, 0, 0], ![0, 0, 0, 2, 0, 0]⟩
  | ⟨true, true, true, false⟩ =>
    ⟨2, 2, ![3, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0]⟩
  | ⟨true, true, true, true⟩ =>
    ⟨3, 1, ![0, 0, 1, 0, 0, 0], ![0, 0, 2, 2, 0, 0]⟩
  | _ => ⟨0, 1, 0, 0⟩

private def forced (t : ReflectionTest) (j : Fin 6) : ℤ :=
  if j = t.pivot then 2 else -t.upper j

private def endpoint (i j : Fin 6) (x : ℤ) : Coordinates := unit j + x • unit i

private def sameOff (i : Fin 6) (c d : Coordinates) : Prop :=
  ∀ j : Fin 6, j ≠ i → c j = d j

private instance (i : Fin 6) (c d : Coordinates) : Decidable (sameOff i c d) :=
  inferInstanceAs (Decidable (∀ j : Fin 6, j ≠ i → c j = d j))

private def validTest (p : BranchMarking) (t : ReflectionTest) : Prop :=
  p.active t.pivot = true ∧ 0 < t.multiple ∧ p.IsProjectedRoot (t.multiple • unit t.pivot) ∧
    (¬ t.multiple ∣ 2 ∨
      (∀ j : Fin 6, p.active j = true → j ≠ t.pivot →
        p.IsProjectedRoot (unit j) ∧ p.IsProjectedRoot (endpoint t.pivot j (t.upper j)) ∧
        (∀ (s : Bool) (n : Fin 36),
          let c := if s then -p.project (positiveCoefficients n) else p.project (positiveCoefficients n)
          sameOff t.pivot c (unit j) → 0 ≤ c t.pivot ∧ c t.pivot ≤ t.upper j)) ∧
      ((∃ j : Fin 6, p.active j = true ∧ j ≠ t.pivot ∧ ¬ t.multiple ∣ forced t j) ∨
        p.IsProjectedRoot t.witness ∧
          ¬ p.IsProjectedRoot (t.witness - (∑ j : Fin 6, t.witness j * forced t j) • unit t.pivot)))

private instance (p : BranchMarking) (t : ReflectionTest) : Decidable (validTest p t) := by
  unfold validTest
  infer_instance

set_option maxHeartbeats 3000000 in
private theorem validTest_of_bad (p : BranchMarking)
    (h : p.innerArmMarked = true ∨ p.centralMarked = true) : validTest p (test p) := by
  obtain ⟨s, a, b, c⟩ := p
  cases s <;> cases a <;> cases b <;> cases c <;> first | decide | (simp at h)

private theorem projectedReflection_endpoint (t : ReflectionTest) (f : Coordinates)
    (hf : t.multiple * f t.pivot = 2) (j : Fin 6) (hj : j ≠ t.pivot) (x : ℤ) :
    endpoint t.pivot j x -
        (t.multiple * ∑ k : Fin 6, endpoint t.pivot j x k * f k) • unit t.pivot =
      endpoint t.pivot j (-x - t.multiple * f j) := by
  have hsum : ∑ k : Fin 6, endpoint t.pivot j x k * f k = f j + x * f t.pivot := by
    simp [endpoint, Pi.add_apply, add_mul, Pi.single_apply,
      ite_mul, mul_ite, Finset.sum_add_distrib]
  rw [hsum]
  ext k
  simp only [endpoint, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  by_cases hk : k = t.pivot
  · subst k
    simp only [hj.symm, ite_false, ite_true, mul_one, zero_add]
    linear_combination -x * hf
  · simp [hk]

private theorem endpoint_sameOff (i j : Fin 6) (x : ℤ) : sameOff i (endpoint i j x) (unit j) := by
  intro k hk
  simp [endpoint, Pi.single_apply, hk]

private theorem endpoint_apply_pivot (i j : Fin 6) (h : j ≠ i) (x : ℤ) : endpoint i j x i = x := by
  simp [endpoint, h.symm]

private theorem not_validTest_of_hasIntegralReflections {p : BranchMarking} {t : ReflectionTest}
    (hp : p.HasIntegralReflections) (ht : validTest p t) : False := by
  obtain ⟨ha, hm, htroot, htest⟩ := ht
  obtain ⟨f, hi, hr⟩ := hp t.pivot t.multiple ha hm htroot
  rcases htest with hdiv | ⟨hfib, hbad⟩
  · exact hdiv ⟨f t.pivot, hi.symm⟩
  have hforced (j : Fin 6) (hj : p.active j = true) : t.multiple * f j = forced t j := by
    by_cases hij : j = t.pivot
    · subst j
      simpa [forced] using hi
    obtain ⟨h₀, h₁, hb⟩ := hfib j hj hij
    have bound {c : Coordinates} (hc : p.IsProjectedRoot c) (h : sameOff t.pivot c (unit j)) :
        0 ≤ c t.pivot ∧ c t.pivot ≤ t.upper j := by
      obtain ⟨s, n, rfl⟩ := hc
      exact hb s n h
    have h₀' : p.IsProjectedRoot (endpoint t.pivot j 0) := by simpa [endpoint] using h₀
    have hl := hr _ h₀'
    have hu := hr _ h₁
    rw [projectedReflection_endpoint t f hi j hij] at hl hu
    have hL := (bound hl (endpoint_sameOff _ _ _)).2
    have hU := (bound hu (endpoint_sameOff _ _ _)).1
    rw [endpoint_apply_pivot _ _ hij] at hL hU
    simp only [forced, ite_eq_right hij]
    omega
  rcases hbad with ⟨j, hj, _, hnd⟩ | ⟨hw, hx⟩
  · exact hnd ⟨f j, (hforced j hj).symm⟩
  · apply hx
    have hsum : t.multiple * ∑ j : Fin 6, t.witness j * f j =
        ∑ j : Fin 6, t.witness j * forced t j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_left_comm]
      by_cases hj : p.active j = true
      · rw [hforced j hj]
      · have hj' : p.active j = false := Bool.eq_false_of_not_eq_true hj
        rw [hw.apply_eq_zero_of_inactive j hj', zero_mul, zero_mul]
    exact hsum ▸ hr _ hw

/-- With the short-arm end unmarked, a crystallographic relative system can
have only the endpoints of the two long arms marked, or have no marks. -/
theorem innerArm_unmarked_and_central_unmarked (p : BranchMarking)
    (h : p.HasIntegralReflections) : p.innerArmMarked = false ∧ p.centralMarked = false := by
  constructor
  · apply Bool.eq_false_of_not_eq_true
    intro hm
    exact not_validTest_of_hasIntegralReflections h (validTest_of_bad p (Or.inl hm))
  · apply Bool.eq_false_of_not_eq_true
    intro hm
    exact not_validTest_of_hasIntegralReflections h (validTest_of_bad p (Or.inr hm))

end BranchMarking

end Langlands.CartanE6Root

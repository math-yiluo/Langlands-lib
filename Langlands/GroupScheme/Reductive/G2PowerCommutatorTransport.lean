import Langlands.GroupScheme.Reductive.B2PowerCommutatorTransport

/-! # The characteristic-three G2 commutator power calculation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.LocalSplitCell

variable {R : Type u} [CommRing R]
    {G : GroupScheme (Spec (CommRingCat.of R))}

/-- The annotated reversed G2 list. The two long-root terms receive
power `3*q`; the two short-root terms receive power `q`. -/
def g2UnequalPowerTerms (F F₃ : Ga R ⟶ Ga R) (q : ℕ)
    (P₁ P₂ P₃ P₄ : Ga R ⟶ G) :
    List (CommTerm R G × CommTermPowerData R) :=
  [((P₄, 1, 2, 3), {
      powerMap := F₃
      exponent := 3 * q
      coefficient := 1
      leftDegree := 2
      rightDegree := 1 }),
    ((P₃, 1, 1, 3), {
      powerMap := F₃
      exponent := 3 * q
      coefficient := 1
      leftDegree := 1
      rightDegree := 1 }),
    ((P₂, -1, 1, 2), {
      powerMap := F
      exponent := q
      coefficient := -1
      leftDegree := 3
      rightDegree := 2 }),
    ((P₁, -1, 1, 1), {
      powerMap := F
      exponent := q
      coefficient := -1
      leftDegree := 3
      rightDegree := 1 })]

@[simp] theorem powerCommTermsWith_g2UnequalPowerTerms
    (F F₃ : Ga R ⟶ Ga R) (q : ℕ) (P₁ P₂ P₃ P₄ : Ga R ⟶ G) :
    powerCommTermsWith (g2UnequalPowerTerms F F₃ q P₁ P₂ P₃ P₄) =
      [(F₃ ≫ P₄, 1, 2, 1), (F₃ ≫ P₃, 1, 1, 1),
        (F ≫ P₂, -1, 3, 2), (F ≫ P₁, -1, 3, 1)] := rfl

/-- Reversal and exact balances give the unequal-power G2 formula
before reordering. Oddness is the explicit sign hypothesis on `q`. -/
theorem g2_unequal_power_commRel_reversed
    (A C P₁ P₂ P₃ P₄ : Ga R ⟶ G)
    (h : CommRel C A
      [(P₁, 1, 1, 1), (P₂, 1, 2, 1), (P₃, -1, 3, 1), (P₄, -1, 3, 2)])
    (F F₃ : Ga R ⟶ Ga R) (q : ℕ) (hq : Odd q)
    (hF : ∀ (Z : Over (Spec (CommRingCat.of R))) (x : Γ(Z.left, ⊤)),
      rootPoint F Z x = VectorGroup.scalarPoint (CommRingCat.of R) Z (x ^ q))
    (hF₃ : ∀ (Z : Over (Spec (CommRingCat.of R))) (x : Γ(Z.left, ⊤)),
      rootPoint F₃ Z x = VectorGroup.scalarPoint (CommRingCat.of R) Z (x ^ (3 * q))) :
    CommRel (F₃ ≫ A) (F ≫ C)
      [(F₃ ≫ P₄, 1, 2, 1), (F₃ ≫ P₃, 1, 1, 1),
        (F ≫ P₂, -1, 3, 2), (F ≫ P₁, -1, 3, 1)] := by
  have hrev : CommRel A C
      [(P₄, 1, 2, 3), (P₃, 1, 1, 3), (P₂, -1, 1, 2), (P₁, -1, 1, 1)] := by
    simpa only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      List.map_cons, List.map_nil, neg_neg] using h.symm
  have hlist : CommRel A C
      ((g2UnequalPowerTerms F F₃ q P₁ P₂ P₃ P₄).map Prod.fst) := hrev
  have hbalance : ∀ t ∈ g2UnequalPowerTerms F F₃ q P₁ P₂ P₃ P₄,
      t.2.IsBalanced (3 * q) q t.1 := by
    intro t ht
    simp only [g2UnequalPowerTerms, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact {
        pointFormula := hF₃
        coefficient_power := one_pow _
        left_balance := by
          change 2 * (3 * q) = (3 * q) * 2
          exact Nat.mul_comm _ _
        right_balance := by simp [Nat.mul_comm] }
    · exact {
        pointFormula := hF₃
        coefficient_power := one_pow _
        left_balance := by simp
        right_balance := by simp [Nat.mul_comm] }
    · exact {
        pointFormula := hF
        coefficient_power := hq.neg_one_pow
        left_balance := by simp
        right_balance := by simp [Nat.mul_comm] }
    · exact {
        pointFormula := hF
        coefficient_power := hq.neg_one_pow
        left_balance := by simp
        right_balance := by simp }
  simpa only [powerCommTermsWith_g2UnequalPowerTerms] using
    hlist.precompose_balanced_powers F₃ F (3 * q) q hF₃ hF hbalance

/-- A coefficient `-3` mixed relation becomes commutation in
characteristic three, over every affine test. -/
theorem g2_pointsCommute_of_mixed_rel
    {w₁ w₂ v : Ga R ⟶ G} {i j : ℕ}
    (h : CommRel w₁ w₂ [(v, -3, i, j)]) (h₃ : (3 : R) = 0) :
    PointsCommute w₁ w₂ :=
  pointsCommute_of_commRel_singleton_zero h (by rw [h₃, neg_zero])

/-- The principal exceptional G2 formula in the standard source
order, with the needed target long-root commutation retained. -/
theorem g2_unequal_power_commRel
    (A C P₁ P₂ P₃ P₄ : Ga R ⟶ G)
    (h : CommRel C A
      [(P₁, 1, 1, 1), (P₂, 1, 2, 1), (P₃, -1, 3, 1), (P₄, -1, 3, 2)])
    (h12 : CommRel P₁ P₂ [(P₄, -3, 1, 1)])
    (h34 : PointsCommute P₃ P₄) (h₃ : (3 : R) = 0)
    (F F₃ : Ga R ⟶ Ga R) (q : ℕ) (hq : Odd q)
    (hF : ∀ (Z : Over (Spec (CommRingCat.of R))) (x : Γ(Z.left, ⊤)),
      rootPoint F Z x = VectorGroup.scalarPoint (CommRingCat.of R) Z (x ^ q))
    (hF₃ : ∀ (Z : Over (Spec (CommRingCat.of R))) (x : Γ(Z.left, ⊤)),
      rootPoint F₃ Z x = VectorGroup.scalarPoint (CommRingCat.of R) Z (x ^ (3 * q))) :
    CommRel (F₃ ≫ A) (F ≫ C)
      [(F₃ ≫ P₃, 1, 1, 1), (F₃ ≫ P₄, 1, 2, 1),
        (F ≫ P₁, -1, 3, 1), (F ≫ P₂, -1, 3, 2)] := by
  have hr := g2_unequal_power_commRel_reversed A C P₁ P₂ P₃ P₄ h F F₃ q hq hF hF₃
  have hs : CommRel (F₃ ≫ A) (F ≫ C)
      [(F₃ ≫ P₃, 1, 1, 1), (F₃ ≫ P₄, 1, 2, 1),
        (F ≫ P₂, -1, 3, 2), (F ≫ P₁, -1, 3, 1)] :=
    CommRel.swap (L₁ := [])
      (L₂ := [(F ≫ P₂, -1, 3, 2), (F ≫ P₁, -1, 3, 1)]) hr
      (h34.symm.precompose_powers F₃ F₃ (3 * q) (3 * q) hF₃ hF₃)
  exact CommRel.swap
    (L₁ := [(F₃ ≫ P₃, 1, 1, 1), (F₃ ≫ P₄, 1, 2, 1)]) (L₂ := []) hs
    ((g2_pointsCommute_of_mixed_rel h12 h₃).symm.precompose_powers F F q q hF hF)

/-- The long-long target mixed formula gives the first source mixed
formula; its two coefficient `-3` terms vanish. -/
theorem g2_mixed_long_power_commRel
    (A P₁ P₂ P₃ P₄ : Ga R ⟶ G)
    (h : CommRel A P₃ [(P₄, -1, 1, 1)]) (h₃ : (3 : R) = 0)
    (F F₃ : Ga R ⟶ Ga R) (q : ℕ)
    (hF₃ : ∀ (Z : Over (Spec (CommRingCat.of R))) (x : Γ(Z.left, ⊤)),
      rootPoint F₃ Z x = VectorGroup.scalarPoint (CommRingCat.of R) Z (x ^ (3 * q))) :
    CommRel (F₃ ≫ A) (F₃ ≫ P₃)
      [(F₃ ≫ P₄, 2, 1, 1), (F ≫ P₁, -3, 2, 1), (F ≫ P₂, -3, 1, 2)] := by
  have htwo : (2 : R) = -1 := by
    apply eq_neg_of_add_eq_zero_left
    linear_combination h₃
  have hn3 : (-3 : R) = 0 := by rw [h₃, neg_zero]
  have hp := h.precompose_power_of_int_coeff hF₃ (by
    intro t ht
    simp only [List.mem_singleton] at ht
    subst t
    exact ⟨-1, by simp⟩)
  intro B _ s x y
  have h' := hp B s x y
  have hz : baseScalar (Over.mk s) (0 : R) = 0 := map_zero _
  simp only [powerCommTerms, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one, termPoint, htwo, hn3] at h' ⊢
  simpa only [hz, zero_mul, rootPoint_zero, mul_one] using h'

/-- The target short-root mixed formula reduces to its coefficient-two
term and gives the source coefficient-minus-one mixed formula. -/
theorem g2_mixed_short_power_commRel
    (C P₁ P₂ P₃ P₄ : Ga R ⟶ G)
    (h : CommRel C P₁
      [(P₂, 2, 1, 1), (P₃, -3, 2, 1), (P₄, -3, 1, 2)])
    (h₃ : (3 : R) = 0)
    (F : Ga R ⟶ Ga R) (q : ℕ)
    (hF : ∀ (Z : Over (Spec (CommRingCat.of R))) (x : Γ(Z.left, ⊤)),
      rootPoint F Z x = VectorGroup.scalarPoint (CommRingCat.of R) Z (x ^ q)) :
    CommRel (F ≫ C) (F ≫ P₁) [(F ≫ P₂, -1, 1, 1)] := by
  have htwo : (2 : R) = -1 := by
    apply eq_neg_of_add_eq_zero_left
    linear_combination h₃
  have hn3 : (-3 : R) = 0 := by rw [h₃, neg_zero]
  have hp := h.precompose_power_of_int_coeff hF (by
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · exact ⟨2, by simp⟩
    · exact ⟨-3, by simp⟩
    · exact ⟨-3, by simp⟩)
  intro B _ s x y
  have h' := hp B s x y
  have hz : baseScalar (Over.mk s) (0 : R) = 0 := map_zero _
  simp only [powerCommTerms, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one, termPoint, htwo, hn3] at h' ⊢
  simpa only [hz, zero_mul, rootPoint_zero, mul_one] using h'

/-- Any needed remaining source mixed relation with coefficient `-3`
follows from the explicitly supplied target commutation. -/
theorem g2_mixed_zero_power_commRel
    (w₁ w₂ v : Ga R ⟶ G) (h : PointsCommute w₁ w₂) (h₃ : (3 : R) = 0)
    (F F₃ : Ga R ⟶ Ga R) (q : ℕ)
    (hF₃ : ∀ (Z : Over (Spec (CommRingCat.of R))) (x : Γ(Z.left, ⊤)),
      rootPoint F₃ Z x = VectorGroup.scalarPoint (CommRingCat.of R) Z (x ^ (3 * q))) :
    CommRel (F₃ ≫ w₁) (F₃ ≫ w₂) [(F ≫ v, -3, 1, 1)] :=
  commRel_singleton_of_coeff_zero
    (h.precompose_powers F₃ F₃ (3 * q) (3 * q) hF₃ hF₃)
    (F ≫ v) (-3) (by rw [h₃, neg_zero]) 1 1

end Langlands.GroupScheme.LocalSplitCell

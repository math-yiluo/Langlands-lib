import Langlands.GroupScheme.Reductive.BalancedPowerCommutatorTransport

/-! # The characteristic-two B2 commutator power calculation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.LocalSplitCell

variable {R : Type u} [CommRing R]
    {G : GroupScheme (Spec (CommRingCat.of R))}

/-- Delete exactly those commutator terms whose scalar coefficient is
zero in the original base ring, retaining the order of the others. -/
def eraseZeroCommTerms (L : List (CommTerm R G)) : List (CommTerm R G) := by
  classical
  exact L.filter fun t => t.2.1 ≠ 0

/-- Zero-coefficient deletion preserves the ordered product of actual
term points on every scheme test. -/
theorem prod_eraseZeroCommTerms (L : List (CommTerm R G))
    (Z : Over (Spec (CommRingCat.of R))) (x y : Γ(Z.left, ⊤)) :
    ((eraseZeroCommTerms L).map (termPoint Z x y)).prod =
      (L.map (termPoint Z x y)).prod := by
  classical
  induction L with
  | nil => rfl
  | cons t L ih =>
    by_cases hc : t.2.1 = 0
    · simpa [eraseZeroCommTerms, hc, termPoint, rootPoint_zero] using ih
    · simpa [eraseZeroCommTerms, hc] using
        congrArg (fun z => termPoint Z x y t * z) ih

/-- Literal commutator formulas admit deletion of zero-coefficient
terms without a nontriviality hypothesis on the base ring. -/
theorem CommRel.erase_zero_terms {w₁ w₂ : Ga R ⟶ G}
    {L : List (CommTerm R G)} (h : CommRel w₁ w₂ L) :
    CommRel w₁ w₂ (eraseZeroCommTerms L) := by
  intro B _ s x y
  rw [prod_eraseZeroCommTerms]
  exact h B s x y

/-- A vanishing singleton commutator term means that the two actual
maps have commuting points. -/
theorem pointsCommute_of_commRel_singleton_zero
    {w₁ w₂ v : Ga R ⟶ G} {c : R} {i j : ℕ}
    (h : CommRel w₁ w₂ [(v, c, i, j)]) (hc : c = 0) :
    PointsCommute w₁ w₂ := by
  have hnil : CommRel w₁ w₂ [] := by
    simpa [eraseZeroCommTerms, hc] using h.erase_zero_terms
  intro B _ s x y
  have h' := hnil B s x y
  simp only [List.map_nil, List.prod_nil] at h'
  exact inv_mul_eq_one.mp h'

/-- Conversely, a zero-coefficient singleton may be inserted into
the commutator formula of two commuting maps. -/
theorem commRel_singleton_of_coeff_zero
    {w₁ w₂ : Ga R ⟶ G} (h : PointsCommute w₁ w₂)
    (v : Ga R ⟶ G) (c : R) (hc : c = 0) (i j : ℕ) :
    CommRel w₁ w₂ [(v, c, i, j)] := by
  intro B _ s x y
  rw [h B s x y, inv_mul_cancel]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    termPoint]
  rw [hc, map_zero, zero_mul, zero_mul, rootPoint_zero]

/-- Commuting points remain commuting after separately supplied
actual power homomorphisms. -/
theorem PointsCommute.precompose_powers
    {w₁ w₂ : Ga R ⟶ G} (h : PointsCommute w₁ w₂)
    (F₁ F₂ : Ga R ⟶ Ga R) (a b : ℕ)
    (hF₁ : ∀ (Z : Over (Spec (CommRingCat.of R))) (x : Γ(Z.left, ⊤)),
      rootPoint F₁ Z x = VectorGroup.scalarPoint (CommRingCat.of R) Z (x ^ a))
    (hF₂ : ∀ (Z : Over (Spec (CommRingCat.of R))) (x : Γ(Z.left, ⊤)),
      rootPoint F₂ Z x = VectorGroup.scalarPoint (CommRingCat.of R) Z (x ^ b)) :
    PointsCommute (F₁ ≫ w₁) (F₂ ≫ w₂) := by
  intro B _ s x y
  simpa only [rootPoint_precompose_power hF₁ w₁ (Over.mk s),
    rootPoint_precompose_power hF₂ w₂ (Over.mk s)] using
    h B s (x ^ a) (y ^ b)

/-- The annotated reversed B2 term list: the long term receives
power `2*q` and degree `(1,1)`, and the short term power `q` and
degree `(2,1)`. The old reversed coefficients are both `-1`. -/
def b2UnequalPowerTerms (F F₂ : Ga R ⟶ Ga R) (q : ℕ) (V W : Ga R ⟶ G) :
    List (CommTerm R G × CommTermPowerData R) :=
  [((W, -1, 1, 2), {
      powerMap := F₂
      exponent := 2 * q
      coefficient := 1
      leftDegree := 1
      rightDegree := 1 }),
    ((V, -1, 1, 1), {
      powerMap := F
      exponent := q
      coefficient := 1
      leftDegree := 2
      rightDegree := 1 })]

@[simp] theorem powerCommTermsWith_b2UnequalPowerTerms
    (F F₂ : Ga R ⟶ Ga R) (q : ℕ) (V W : Ga R ⟶ G) :
    powerCommTermsWith (b2UnequalPowerTerms F F₂ q V W) =
      [(F₂ ≫ W, 1, 1, 1), (F ≫ V, 1, 2, 1)] := rfl

/-- The exceptional B2 power transport in characteristic two.
The target short-long formula becomes the source short-long formula
with the two root lengths exchanged. No root-group identifications
or commutation premises are suppressed. -/
theorem b2_unequal_power_commRel
    (A C V W : Ga R ⟶ G)
    (h : CommRel C A [(V, 1, 1, 1), (W, 1, 2, 1)])
    (h₂ : (2 : R) = 0)
    (F F₂ : Ga R ⟶ Ga R) (q : ℕ)
    (hF : ∀ (Z : Over (Spec (CommRingCat.of R))) (x : Γ(Z.left, ⊤)),
      rootPoint F Z x = VectorGroup.scalarPoint (CommRingCat.of R) Z (x ^ q))
    (hF₂ : ∀ (Z : Over (Spec (CommRingCat.of R))) (x : Γ(Z.left, ⊤)),
      rootPoint F₂ Z x = VectorGroup.scalarPoint (CommRingCat.of R) Z (x ^ (2 * q))) :
    CommRel (F₂ ≫ A) (F ≫ C) [(F₂ ≫ W, 1, 1, 1), (F ≫ V, 1, 2, 1)] := by
  have hneg : (-1 : R) = 1 := by
    apply Eq.symm
    apply eq_neg_of_add_eq_zero_left
    simpa only [one_add_one_eq_two] using h₂
  have hrev : CommRel A C [(W, -1, 1, 2), (V, -1, 1, 1)] := by
    simpa only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      List.map_cons, List.map_nil] using h.symm
  have hlist : CommRel A C ((b2UnequalPowerTerms F F₂ q V W).map Prod.fst) := hrev
  have hbalance : ∀ t ∈ b2UnequalPowerTerms F F₂ q V W,
      t.2.IsBalanced (2 * q) q t.1 := by
    intro t ht
    simp only [b2UnequalPowerTerms, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact {
        pointFormula := hF₂
        coefficient_power := by simpa only [one_pow] using hneg.symm
        left_balance := by simp
        right_balance := by simp [Nat.mul_comm] }
    · exact {
        pointFormula := hF
        coefficient_power := by simpa only [one_pow] using hneg.symm
        left_balance := by simp
        right_balance := by simp }
  simpa only [powerCommTermsWith_b2UnequalPowerTerms] using
    hlist.precompose_balanced_powers F₂ F (2 * q) q hF₂ hF hbalance

/-- The same formula with its two output terms exchanged, under the
explicit target commutation premise. -/
theorem b2_unequal_power_commRel_reordered
    (A C V W : Ga R ⟶ G)
    (h : CommRel C A [(V, 1, 1, 1), (W, 1, 2, 1)])
    (h₂ : (2 : R) = 0) (hVW : PointsCommute V W)
    (F F₂ : Ga R ⟶ Ga R) (q : ℕ)
    (hF : ∀ (Z : Over (Spec (CommRingCat.of R))) (x : Γ(Z.left, ⊤)),
      rootPoint F Z x = VectorGroup.scalarPoint (CommRingCat.of R) Z (x ^ q))
    (hF₂ : ∀ (Z : Over (Spec (CommRingCat.of R))) (x : Γ(Z.left, ⊤)),
      rootPoint F₂ Z x = VectorGroup.scalarPoint (CommRingCat.of R) Z (x ^ (2 * q))) :
    CommRel (F₂ ≫ A) (F ≫ C) [(F ≫ V, 1, 2, 1), (F₂ ≫ W, 1, 1, 1)] :=
  CommRel.swap (L₁ := []) (L₂ := [])
    (b2_unequal_power_commRel A C V W h h₂ F F₂ q hF hF₂)
    (hVW.symm.precompose_powers F₂ F (2 * q) q hF₂ hF)

/-- The coefficient-two target mixed relation gives commuting actual
short-root points in characteristic two. -/
theorem b2_pointsCommute_of_mixed_rel
    {C V W : Ga R ⟶ G}
    (h : CommRel C V [(W, 2, 1, 1)]) (h₂ : (2 : R) = 0) :
    PointsCommute C V :=
  pointsCommute_of_commRel_singleton_zero h h₂

/-- The source mixed B2 relation with coefficient two holds for the
powered long target maps whenever those target maps commute.
That target commutation is retained as an explicit hypothesis. -/
theorem b2_mixed_unequal_power_commRel
    (A V W : Ga R ⟶ G) (hAW : PointsCommute A W) (h₂ : (2 : R) = 0)
    (F F₂ : Ga R ⟶ Ga R) (q : ℕ)
    (hF₂ : ∀ (Z : Over (Spec (CommRingCat.of R))) (x : Γ(Z.left, ⊤)),
      rootPoint F₂ Z x = VectorGroup.scalarPoint (CommRingCat.of R) Z (x ^ (2 * q))) :
    CommRel (F₂ ≫ A) (F₂ ≫ W) [(F ≫ V, 2, 1, 1)] :=
  commRel_singleton_of_coeff_zero
    (hAW.precompose_powers F₂ F₂ (2 * q) (2 * q) hF₂ hF₂)
    (F ≫ V) 2 h₂ 1 1

end Langlands.GroupScheme.LocalSplitCell

import Langlands.Global.RepresentationHeightDominationProof

/-! # Polynomial growth independent of a closed matrix embedding -/

noncomputable section

universe u v

open AlgebraicGeometry

namespace Langlands.Global.RepresentationGrowth

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) {N M : ℕ}
  (rho : GroupScheme.MatrixRepresentation G (Fin N))
  (sigma : GroupScheme.MatrixRepresentation G (Fin M))

/-- Growth for any matrix representation implies growth for the height of a
closed matrix embedding. The new degree is chosen before the point. -/
theorem HasPolynomialGrowth.of_closedImmersion
    (hrho : GroupScheme.IsClosedSubgroup rho)
    {f : InfiniteAdelicGroupPoints F G → ℂ}
    (hf : HasPolynomialGrowth F G sigma f) :
    HasPolynomialGrowth F G rho f := by
  obtain ⟨D, hD, e, hdom⟩ :=
    closedImmersionHeightDomination F G N M rho sigma hrho
  obtain ⟨C, hC, d, hf⟩ := hf
  refine ⟨C * D ^ d, mul_nonneg hC (pow_nonneg (zero_le_one.trans hD) d),
    e * d, fun g => ?_⟩
  calc
    ‖f g‖ ≤ C * height F G sigma g ^ d := hf g
    _ ≤ C * (D * height F G rho g ^ e) ^ d :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (height_nonneg F G sigma g) (hdom g) d) hC
    _ = (C * D ^ d) * height F G rho g ^ (e * d) := by
      rw [mul_pow, pow_mul]
      ring

/-- Two closed matrix embeddings give exactly the same polynomial-growth
predicate on the original infinite adelic group. -/
theorem hasPolynomialGrowth_iff_of_closedImmersions
    (hrho : GroupScheme.IsClosedSubgroup rho)
    (hsigma : GroupScheme.IsClosedSubgroup sigma)
    (f : InfiniteAdelicGroupPoints F G → ℂ) :
    HasPolynomialGrowth F G rho f ↔ HasPolynomialGrowth F G sigma f :=
  ⟨HasPolynomialGrowth.of_closedImmersion F G sigma rho hsigma,
    HasPolynomialGrowth.of_closedImmersion F G rho sigma hrho⟩

/-- The submodules are equal inside the unchanged ambient function module. -/
theorem polynomialGrowthFunctions_eq_of_closedImmersions
    (hrho : GroupScheme.IsClosedSubgroup rho)
    (hsigma : GroupScheme.IsClosedSubgroup sigma) :
    polynomialGrowthFunctions F G rho = polynomialGrowthFunctions F G sigma := by
  ext f
  exact hasPolynomialGrowth_iff_of_closedImmersions F G rho sigma hrho hsigma f

/-- The change of closed matrix embedding is the identity on actual functions. -/
def polynomialGrowthChangeRepresentation
    (hrho : GroupScheme.IsClosedSubgroup rho)
    (hsigma : GroupScheme.IsClosedSubgroup sigma) :
    ↥(polynomialGrowthFunctions F G rho) ≃ₗ[ℂ] ↥(polynomialGrowthFunctions F G sigma) where
  toFun f := ⟨f.val,
    (hasPolynomialGrowth_iff_of_closedImmersions F G rho sigma hrho hsigma f.val).mp f.property⟩
  invFun f := ⟨f.val,
    (hasPolynomialGrowth_iff_of_closedImmersions F G rho sigma hrho hsigma f.val).mpr f.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem polynomialGrowthChangeRepresentation_apply
    (hrho : GroupScheme.IsClosedSubgroup rho)
    (hsigma : GroupScheme.IsClosedSubgroup sigma)
    (f : ↥(polynomialGrowthFunctions F G rho)) :
    (polynomialGrowthChangeRepresentation F G rho sigma hrho hsigma f).val = f.val := rfl

/-- The identity comparison intertwines the original positive right actions. -/
theorem polynomialGrowthChangeRepresentation_rightAction
    (hrho : GroupScheme.IsClosedSubgroup rho)
    (hsigma : GroupScheme.IsClosedSubgroup sigma)
    (f : ↥(polynomialGrowthFunctions F G rho)) (g : InfiniteAdelicGroupPoints F G) :
    polynomialGrowthChangeRepresentation F G rho sigma hrho hsigma
        (polynomialGrowthRightAction F G rho g f) =
      polynomialGrowthRightAction F G sigma g
        (polynomialGrowthChangeRepresentation F G rho sigma hrho hsigma f) := rfl

/-- A common exponent for an arbitrary family transfers through a closed
embedding; its constants may depend on the family index. -/
theorem uniformPolynomialBound_of_closedImmersion
    (hrho : GroupScheme.IsClosedSubgroup rho) {J : Type v}
    (f : J → InfiniteAdelicGroupPoints F G → ℂ)
    (hf : ∃ d : ℕ, ∀ j, ∃ C : ℝ, 0 ≤ C ∧ ∀ g,
      ‖f j g‖ ≤ C * height F G sigma g ^ d) :
    ∃ d : ℕ, ∀ j, ∃ C : ℝ, 0 ≤ C ∧ ∀ g,
      ‖f j g‖ ≤ C * height F G rho g ^ d := by
  obtain ⟨D, hD, e, hdom⟩ :=
    closedImmersionHeightDomination F G N M rho sigma hrho
  obtain ⟨d, hf⟩ := hf
  refine ⟨e * d, fun j => ?_⟩
  obtain ⟨C, hC, hj⟩ := hf j
  refine ⟨C * D ^ d, mul_nonneg hC (pow_nonneg (zero_le_one.trans hD) d),
    fun g => ?_⟩
  calc
    ‖f j g‖ ≤ C * height F G sigma g ^ d := hj g
    _ ≤ C * (D * height F G rho g ^ e) ^ d :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (height_nonneg F G sigma g) (hdom g) d) hC
    _ = (C * D ^ d) * height F G rho g ^ (e * d) := by
      rw [mul_pow, pow_mul]
      ring

/-- Independence also preserves the order of the common-exponent and
index-dependent-constant quantifiers. -/
theorem uniformPolynomialBound_iff_of_closedImmersions
    (hrho : GroupScheme.IsClosedSubgroup rho)
    (hsigma : GroupScheme.IsClosedSubgroup sigma) {J : Type v}
    (f : J → InfiniteAdelicGroupPoints F G → ℂ) :
    (∃ d : ℕ, ∀ j, ∃ C : ℝ, 0 ≤ C ∧ ∀ g,
      ‖f j g‖ ≤ C * height F G rho g ^ d) ↔
    (∃ d : ℕ, ∀ j, ∃ C : ℝ, 0 ≤ C ∧ ∀ g,
      ‖f j g‖ ≤ C * height F G sigma g ^ d) :=
  ⟨uniformPolynomialBound_of_closedImmersion F G sigma rho hsigma f,
    uniformPolynomialBound_of_closedImmersion F G rho sigma hrho f⟩

end Langlands.Global.RepresentationGrowth

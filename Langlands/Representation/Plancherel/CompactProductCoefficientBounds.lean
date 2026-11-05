import Langlands.Representation.Plancherel.CompactProductInducedCoefficients

/-! # Finite compact values and bounds for actual product coefficients -/

noncomputable section

open Langlands.Aubert.General
open scoped TensorProduct NNReal

namespace Langlands.Plancherel

universe uG uV

section TensorBounds

variable {L : Type uG} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  (A : SmoothRep.{0, uG, uV} ℂ L) (ξ : L → ℝ)
  (hξ : ∀ m, 0 ≤ ξ m)
  (hcoeff : ∀ (v : A) (ℓ : SmoothDual A.representation),
    ∃ C : ℝ, 0 < C ∧ ∀ m, ‖ℓ.val (A.representation m v)‖ ≤ C * ξ m)

include hcoeff in
/-- Pure matrix-coefficient bounds extend to every algebraic coefficient tensor. -/
theorem coefficientTensorMap_bound (t : CoefficientTensor A) :
    ∃ C : ℝ, 0 < C ∧ ∀ m, ‖coefficientTensorMap A t m‖ ≤ C * ξ m := by
  induction t using TensorProduct.inductionOn with
  | tmul v ℓ => exact hcoeff v ℓ
  | add t s ht hs =>
    obtain ⟨C, hC, ht⟩ := ht
    obtain ⟨D, hD, hs⟩ := hs
    refine ⟨C + D, add_pos hC hD, fun m => ?_⟩
    calc
      ‖coefficientTensorMap A (t + s) m‖ =
          ‖coefficientTensorMap A t m + coefficientTensorMap A s m‖ := by
        rw [map_add, LocallyConstant.add_apply]
      _ ≤ ‖coefficientTensorMap A t m‖ + ‖coefficientTensorMap A s m‖ := norm_add_le _ _
      _ ≤ C * ξ m + D * ξ m := add_le_add (ht m) (hs m)
      _ = (C + D) * ξ m := (add_mul _ _ _).symm

include hξ hcoeff in
/-- A finite set of tensors has a single positive coefficient-bound constant. -/
theorem coefficientTensorMap_bound_finite (S : Set (CoefficientTensor A))
    (hS : S.Finite) :
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ S, ∀ m, ‖coefficientTensorMap A t m‖ ≤ C * ξ m := by
  choose c hcpos hc using coefficientTensorMap_bound A ξ hcoeff
  obtain ⟨B, hB⟩ := (hS.image c).bddAbove
  refine ⟨max 1 B, lt_max_of_lt_left zero_lt_one, ?_⟩
  intro t ht m
  exact (hc t m).trans
    (mul_le_mul_of_nonneg_right
      ((hB ⟨t, ht, rfl⟩).trans (le_max_right 1 B)) (hξ m))

end TensorBounds

namespace CompactInduction

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (A : SmoothRep.{0, uG, uV} ℂ M) (K : OpenSubgroup G)

/-- Restrict the actual product-induced function to the compact product. -/
def compactValue (F : productInducedCoefficientObject h hU A) (k : K × K) :
    CoefficientTensor A :=
  Induction.eval (P.prod P)
    (inducingRepresentation (h.prod h) (hU.prod hU)
      (productLeviObject A A.contragredient)) F ((k.1 : G), (k.2 : G))

/-- Compact values are locally constant before any coefficient bound is used. -/
theorem compactValue_isLocallyConstant (F : productInducedCoefficientObject h hU A) :
    IsLocallyConstant (compactValue h hU A K F) :=
  (Induction.eval_isLocallyConstant (P.prod P)
    (inducingRepresentation (h.prod h) (hU.prod hU)
      (productLeviObject A A.contragredient)) F).comp_continuous
    (continuous_subtype_val.prodMap continuous_subtype_val)

/-- There are only finitely many actual tensor values on K × K. -/
theorem compactValue_range_finite (hK : IsCompact (K : Set G))
    (F : productInducedCoefficientObject h hU A) :
    (Set.range (compactValue h hU A K F)).Finite := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  exact (compactValue_isLocallyConstant h hU A K F).range_finite

variable [SecondCountableTopology G]

set_option backward.isDefEq.respectTransparency.types false in
/-- Contracting the first parabolic coordinate gives the actual Levi coefficient
and the positive induction half-character. -/
theorem contraction_inducing (q : P) (t : CoefficientTensor A) :
    TensorProduct.lift (smoothDualPairing A.representation).flip
        (inducingRepresentation (h.prod h) (hU.prod hU)
          (productLeviObject A A.contragredient)
          ⟨((q : G), 1), q.2, P.one_mem⟩ t) =
      (HaarModulus.closedHalfCharacter U hU P h.le_normalizer q : ℂ) *
        coefficientTensorMap A t (h.projection q) := by
  rw [product_inducingRepresentation h h hU hU A A.contragredient]
  induction t using TensorProduct.inductionOn with
  | tmul v ℓ =>
    change TensorProduct.lift (smoothDualPairing A.representation).flip
      (inducingRepresentation h hU A q v ⊗ₜ[ℂ]
        inducingRepresentation h hU A.contragredient 1 ℓ) = _
    rw [map_one, Module.End.one_apply]
    change ℓ.val ((HaarModulus.closedHalfCharacter U hU P h.le_normalizer q : ℂ) •
      A.representation (h.projection q) v) = _
    exact map_smul ℓ.val _ _
  | add t s ht hs =>
    let T : CoefficientTensor A →ₗ[ℂ] CoefficientTensor A :=
      Induction.BinaryTensor.inducing P P
        (inducingRepresentation h hU A) (inducingRepresentation h hU A.contragredient)
        ⟨((q : G), 1), q.2, P.one_mem⟩
    let e := TensorProduct.lift (smoothDualPairing A.representation).flip
    have ha : e (T (t + s)) = e (T t) + e (T s) :=
      (congrArg e (map_add T t s)).trans (map_add e (T t) (T s))
    calc
      _ = e (T t) + e (T s) := ha
      _ = _ := congrArg₂ (· + ·) ht hs
      _ = _ := by rw [map_add, LocallyConstant.add_apply, mul_add]

set_option backward.isDefEq.respectTransparency.types false in
/-- Original function covariance gives the diagonal formula for every
parabolic–compact factorization of k*g. -/
theorem integrand_factorization
    (F : productInducedCoefficientObject h hU A) (g : G) (k k₁ : K) (q : P)
    (he : (k : G) * g = (q : G) * (k₁ : G)) :
    integrand h hU A K g F k =
      (HaarModulus.closedHalfCharacter U hU P h.le_normalizer q : ℂ) *
        coefficientTensorMap A (compactValue h hU A K F (k₁, k)) (h.projection q) := by
  change TensorProduct.lift (smoothDualPairing A.representation).flip
    (Induction.eval (P.prod P)
      (inducingRepresentation (h.prod h) (hU.prod hU)
        (productLeviObject A A.contragredient)) F ((k : G) * g, k)) = _
  rw [he]
  have hcov := Induction.eval_covariant (P.prod P)
    (inducingRepresentation (h.prod h) (hU.prod hU)
      (productLeviObject A A.contragredient)) F
    ⟨((q : G), 1), q.2, P.one_mem⟩ ((k₁ : G), (k : G))
  simp only [Prod.mk_mul_mk, one_mul] at hcov
  exact (congrArg (fun t : CoefficientTensor A =>
    TensorProduct.lift (smoothDualPairing A.representation).flip t) hcov).trans
      (contraction_inducing h hU A q _)

/-- A pure Levi coefficient estimate yields one constant for the original
diagonal integrand, uniform in g, k and every parabolic–compact factorization. -/
theorem integrand_bound (hK : IsCompact (K : Set G))
    (ξ : M → ℝ) (hξ : ∀ m, 0 ≤ ξ m)
    (hcoeff : ∀ (v : A) (ℓ : SmoothDual A.representation),
      ∃ C : ℝ, 0 < C ∧ ∀ m, ‖ℓ.val (A.representation m v)‖ ≤ C * ξ m)
    (F : productInducedCoefficientObject h hU A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (g : G) (k k₁ : K) (q : P),
      (k : G) * g = (q : G) * (k₁ : G) →
      ‖integrand h hU A K g F k‖ ≤
        ‖(HaarModulus.closedHalfCharacter U hU P h.le_normalizer q : ℂ)‖ *
          (C * ξ (h.projection q)) := by
  obtain ⟨C, hC, hb⟩ := coefficientTensorMap_bound_finite A ξ hξ hcoeff
    (Set.range (compactValue h hU A K F)) (compactValue_range_finite h hU A K hK F)
  refine ⟨C, hC, ?_⟩
  intro g k k₁ q he
  rw [integrand_factorization h hU A K F g k k₁ q he, norm_mul]
  exact mul_le_mul_of_nonneg_left
    (hb _ ⟨(k₁, k), rfl⟩ _) (norm_nonneg _)

/-- For unimodular U, the same bound uses the positive square root of the
actual Levi Haar modulus, as in the compact integral estimate. -/
theorem integrand_bound_levi (hδ : IsUnimodularModulus U hU)
    (hK : IsCompact (K : Set G))
    (ξ : M → ℝ) (hξ : ∀ m, 0 ≤ ξ m)
    (hcoeff : ∀ (v : A) (ℓ : SmoothDual A.representation),
      ∃ C : ℝ, 0 < C ∧ ∀ m, ‖ℓ.val (A.representation m v)‖ ≤ C * ξ m)
    (F : productInducedCoefficientObject h hU A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (g : G) (k k₁ : K) (q : P),
      (k : G) * g = (q : G) * (k₁ : G) →
      ‖integrand h hU A K g F k‖ ≤
        (NNReal.sqrt
          (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer
            (h.projection q) : ℝ≥0) : ℝ) * (C * ξ (h.projection q)) := by
  obtain ⟨C, hC, hb⟩ := integrand_bound h hU A K hK ξ hξ hcoeff F
  refine ⟨C, hC, ?_⟩
  intro g k k₁ q he
  have hn : ‖(HaarModulus.closedHalfCharacter U hU P h.le_normalizer q : ℂ)‖ =
      (NNReal.sqrt
        (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer
          (h.projection q) : ℝ≥0) : ℝ) := by
    rw [closedHalfCharacter_eq_comp_projection h hU hδ, MonoidHom.comp_apply]
    change ‖(((NNReal.sqrt
      (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer
        (h.projection q) : ℝ≥0) : ℝ) : ℂ))‖ = _
    rw [Complex.norm_real, Real.norm_of_nonneg (NNReal.coe_nonneg _)]
  simpa only [hn] using hb g k k₁ q he

end CompactInduction

end Langlands.Plancherel

import Langlands.Representation.RankinSelberg.AnalyticBridge
import Langlands.Representation.RankinSelberg.FunctionalEquationStatement

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear Polynomial QuotientIntegration

universe uF uV uW

section Models

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] {n : ℕ}
  (ψ : UnitaryAdditiveCharacter F)
  (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)

/-- The Weyl-translated functional, expressed for the inverse additive character. -/
def firstDualFunctional (ℓ : glFunctionals ψ n π) :
    glFunctionals (ψ.scale (-1)) n (inverseTransposePullback π) :=
  functionalsCongr (standardCharacter_scale_neg_one ψ n).symm (dualFunctional ψ π ℓ)

/-- The corresponding second functional has the inverse of the inverse character. -/
def secondDualFunctional (ℓ : glInverseFunctionals ψ n π) :
    glInverseFunctionals (ψ.scale (-1)) n (inverseTransposePullback π) :=
  dualFunctional (ψ.scale (-1)) π
    (functionalsCongr (standardCharacter_scale_neg_one ψ n).symm ℓ)

theorem firstDualFunctional_ne_zero {ℓ : glFunctionals ψ n π} (hℓ : ℓ.val ≠ 0) :
    (firstDualFunctional ψ π ℓ).val ≠ 0 :=
  dualFunctional_nonzero ψ π ℓ hℓ

theorem secondDualFunctional_ne_zero {ℓ : glInverseFunctionals ψ n π} (hℓ : ℓ.val ≠ 0) :
    (secondDualFunctional ψ π ℓ).val ≠ 0 :=
  dualFunctional_nonzero (ψ.scale (-1)) π _ hℓ

theorem firstDualFunction_coefficient (ℓ : glFunctionals ψ n π) (v : V) :
    firstDualFunction ψ n (coefficientMap π ℓ v) =
      coefficientMap (inverseTransposePullback π) (firstDualFunctional ψ π ℓ) v := by
  apply Subtype.ext
  exact dualFunction_coefficient ψ π ℓ v

theorem secondDualFunction_coefficient (ℓ : glInverseFunctionals ψ n π) (v : V) :
    secondDualFunction ψ n (coefficientMap π ℓ v) =
      coefficientMap (inverseTransposePullback π) (secondDualFunctional ψ π ℓ) v := by
  apply Subtype.ext
  exact dualFunction_coefficient (ψ.scale (-1)) π
    (functionalsCongr (standardCharacter_scale_neg_one ψ n).symm ℓ) v

/-- Transform the first actual coefficient image into its inverse-transpose image. -/
def firstDualModelMap (ℓ : glFunctionals ψ n π) :
    (coefficientModel π ℓ).toSubmodule →ₗ[ℂ]
      (coefficientModel (inverseTransposePullback π) (firstDualFunctional ψ π ℓ)).toSubmodule where
  toFun f := ⟨firstDualFunction ψ n f.val, by
    obtain ⟨v, hv⟩ := f.property
    exact ⟨v, (firstDualFunction_coefficient ψ π ℓ v).symm.trans (congrArg _ hv)⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Transform the second actual coefficient image into its inverse-transpose image. -/
def secondDualModelMap (ℓ : glInverseFunctionals ψ n π) :
    (coefficientModel π ℓ).toSubmodule →ₗ[ℂ]
      (coefficientModel (inverseTransposePullback π) (secondDualFunctional ψ π ℓ)).toSubmodule where
  toFun f := ⟨secondDualFunction ψ n f.val, by
    obtain ⟨v, hv⟩ := f.property
    exact ⟨v, (secondDualFunction_coefficient ψ π ℓ v).symm.trans (congrArg _ hv)⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem firstDualModelMap_bijective (ℓ : glFunctionals ψ n π) :
    Function.Bijective (firstDualModelMap ψ π ℓ) := by
  constructor
  · intro f g hfg
    apply Subtype.ext
    apply Subtype.ext
    apply (dualFunction n).injective
    exact congrArg (fun f => f.val.val) hfg
  · intro f
    obtain ⟨v, hv⟩ := f.property
    refine ⟨modelMap π ℓ v, Subtype.ext ?_⟩
    exact (firstDualFunction_coefficient ψ π ℓ v).trans hv

theorem secondDualModelMap_bijective (ℓ : glInverseFunctionals ψ n π) :
    Function.Bijective (secondDualModelMap ψ π ℓ) := by
  constructor
  · intro f g hfg
    apply Subtype.ext
    apply Subtype.ext
    apply (dualFunction n).injective
    exact congrArg (fun f => f.val.val) hfg
  · intro f
    obtain ⟨v, hv⟩ := f.property
    refine ⟨modelMap π ℓ v, Subtype.ext ?_⟩
    exact (secondDualFunction_coefficient ψ π ℓ v).trans hv

/-- Actual first-model equivalence, with no multiplicity-one assumption. -/
def firstDualModelEquiv (ℓ : glFunctionals ψ n π) :
    (coefficientModel π ℓ).toSubmodule ≃ₗ[ℂ]
      (coefficientModel (inverseTransposePullback π) (firstDualFunctional ψ π ℓ)).toSubmodule :=
  LinearEquiv.ofBijective (firstDualModelMap ψ π ℓ) (firstDualModelMap_bijective ψ π ℓ)

/-- Actual second-model equivalence, with no multiplicity-one assumption. -/
def secondDualModelEquiv (ℓ : glInverseFunctionals ψ n π) :
    (coefficientModel π ℓ).toSubmodule ≃ₗ[ℂ]
      (coefficientModel (inverseTransposePullback π) (secondDualFunctional ψ π ℓ)).toSubmodule :=
  LinearEquiv.ofBijective (secondDualModelMap ψ π ℓ) (secondDualModelMap_bijective ψ π ℓ)

/-- Right translation is an automorphism of each actual coefficient image. -/
def translateModelEquiv (ℓ : glFunctionals ψ n π)
    (a : Langlands.GeneralLinear (n + 1) F) :
    (coefficientModel π ℓ).toSubmodule ≃ₗ[ℂ] (coefficientModel π ℓ).toSubmodule where
  toLinearMap := modelRepresentation π ℓ a
  invFun := modelRepresentation π ℓ a⁻¹
  left_inv f := by
    change (modelRepresentation π ℓ a⁻¹ * modelRepresentation π ℓ a) f = f
    rw [← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  right_inv f := by
    change (modelRepresentation π ℓ a * modelRepresentation π ℓ a⁻¹) f = f
    rw [← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

omit [IsTopologicalRing F] in
@[simp] theorem translateModelEquiv_val (ℓ : glFunctionals ψ n π)
    (a : Langlands.GeneralLinear (n + 1) F) (f : (coefficientModel π ℓ).toSubmodule) :
    (translateModelEquiv ψ π ℓ a f).val = translateWhittaker ψ n f.val a := rfl

/-- Dual transformation followed by any right translation remains an equivalence
onto the full inverse-transpose coefficient model. -/
def translatedFirstDualModelEquiv (ℓ : glFunctionals ψ n π)
    (a : Langlands.GeneralLinear (n + 1) F) :
    (coefficientModel π ℓ).toSubmodule ≃ₗ[ℂ]
      (coefficientModel (inverseTransposePullback π) (firstDualFunctional ψ π ℓ)).toSubmodule :=
  (firstDualModelEquiv ψ π ℓ).trans
    (translateModelEquiv (ψ.scale (-1)) (inverseTransposePullback π)
      (firstDualFunctional ψ π ℓ) a)

@[simp] theorem translatedFirstDualModelEquiv_val (ℓ : glFunctionals ψ n π)
    (a : Langlands.GeneralLinear (n + 1) F) (f : (coefficientModel π ℓ).toSubmodule) :
    (translatedFirstDualModelEquiv ψ π ℓ a f).val =
      translateWhittaker (ψ.scale (-1)) n (firstDualFunction ψ n f.val) a := rfl

end Models

section EqualRank

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (q : ℕ) (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
  {n : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]
  (μ : Measure (LeftUnipotentQuotient n F))
  (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
  (ℓ : glFunctionals ψ n π) (ℓ' : glInverseFunctionals ψ n σ)

/-- The full transformed family equals the rational-value family of the actual
inverse-transpose models. The tests already range over every Schwartz function. -/
theorem dualEqualRankRationalValues_eq :
    dualEqualRankRationalValues q ψ abv μ π σ ℓ ℓ' =
      equalRankRationalValues q (ψ.scale (-1)) abv μ
        (inverseTransposePullback π) (inverseTransposePullback σ)
        (firstDualFunctional ψ π ℓ) (secondDualFunctional ψ σ ℓ') := by
  ext R
  constructor
  · rintro ⟨f, f', Φ, hR⟩
    exact ⟨firstDualModelMap ψ π ℓ f, secondDualModelMap ψ σ ℓ' f', Φ, hR⟩
  · rintro ⟨g, g', Φ, hR⟩
    obtain ⟨f, rfl⟩ := (firstDualModelMap_bijective ψ π ℓ).surjective g
    obtain ⟨f', rfl⟩ := (secondDualModelMap_bijective ψ σ ℓ').surjective g'
    exact ⟨f, f', Φ, hR⟩

/-- Under Whittaker type and half-plane convergence for the transformed models,
the dual intrinsic zeta set is exactly the transformed rational-value set. -/
theorem dualEqualRankZetaValues_eq_rationalValues
    (hπ : IsOfWhittakerType n (standardCharacter (ψ.scale (-1)) n)
      (inverseTransposePullback π))
    (hσ : IsOfWhittakerType n (inverseStandardCharacter (ψ.scale (-1)) n)
      (inverseTransposePullback σ))
    (hℓ : ℓ.val ≠ 0) (hℓ' : ℓ'.val ≠ 0)
    (hconv : ∀ f : (coefficientModel (inverseTransposePullback π)
        (firstDualFunctional ψ π ℓ)).toSubmodule,
      ∀ f' : (coefficientModel (inverseTransposePullback σ)
        (secondDualFunctional ψ σ ℓ')).toSubmodule,
      ∀ Φ : SchwartzBruhat (Fin (n + 1) → F),
        ∃ a : ℝ, ∀ s : ℂ, a < s.re →
          EqualRankConverges (ψ.scale (-1)) abv μ f.val f'.val Φ s) :
    dualEqualRankZetaValues q ψ abv μ π σ =
      dualEqualRankRationalValues q ψ abv μ π σ ℓ ℓ' := by
  rw [dualEqualRankRationalValues_eq]
  exact equalRankZetaValues_eq_rationalValues q (ψ.scale (-1)) abv μ hπ hσ
    (firstDualFunctional_ne_zero ψ π hℓ) (secondDualFunctional_ne_zero ψ σ hℓ') hconv

/-- A dual analytic conclusion compares the intrinsic L-polynomial with the
normalized generator used in the equal-rank functional equation. -/
theorem dualEqualRank_isLPolynomial_iff
    (hπ : IsOfWhittakerType n (standardCharacter (ψ.scale (-1)) n)
      (inverseTransposePullback π))
    (hσ : IsOfWhittakerType n (inverseStandardCharacter (ψ.scale (-1)) n)
      (inverseTransposePullback σ))
    (hℓ : ℓ.val ≠ 0) (hℓ' : ℓ'.val ≠ 0)
    (h : EqualRankAnalyticConclusion q (ψ.scale (-1)) abv μ
      (inverseTransposePullback π) (inverseTransposePullback σ)
      (firstDualFunctional ψ π ℓ) (secondDualFunctional ψ σ ℓ')) (P : ℂ[X]) :
    IsEqualRankLPolynomial q (ψ.scale (-1)) abv μ
        (inverseTransposePullback π) (inverseTransposePullback σ) P ↔
      IsNormalizedGenerator (dualEqualRankRationalValues q ψ abv μ π σ ℓ ℓ') P := by
  rw [dualEqualRankRationalValues_eq]
  exact h.isEqualRankLPolynomial_iff hπ hσ
    (firstDualFunctional_ne_zero ψ π hℓ) (secondDualFunctional_ne_zero ψ σ hℓ') P

end EqualRank

section UnequalRank

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [MeasurableSpace F]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {n r : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]

omit [IsTopologicalRing F] in
/-- Unfold the fixed-rank wrapper without imposing an arithmetic normal form on
the larger rank. Only the equality of natural-number dimensions is transported. -/
theorem unequalRankValuesAt_eq_set (j k : ℕ) (hr : r = n + (j + k + 1))
    (q : ℕ) (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    (μ : Measure (LeftUnipotentQuotient n F))
    (ν : Measure (Matrix (Fin j) (Fin (n + 1)) F))
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (ℓ : glFunctionals ψ r π) (ℓ' : glInverseFunctionals ψ n σ) :
    unequalRankValuesAt j k hr q ψ abv μ ν π σ ℓ ℓ' =
      {R | ∃ f : (coefficientModel π ℓ).toSubmodule,
        ∃ f' : (coefficientModel σ ℓ').toSubmodule,
          HasRationalContinuation q
            (unequalRankIntegralAt j k hr ψ abv μ ν f.val f'.val) R} := by
  subst r
  rfl

/-- The Weyl-translated dual family is the whole rational-value family for the
inverse-transpose pair with the rectangular blocks exchanged. -/
theorem dualUnequalRankRationalValuesAt_eq (hnr : n < r)
    (j k : ℕ) (hr : r = n + (j + k + 1))
    (q : ℕ) (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    (μ : Measure (LeftUnipotentQuotient n F)) (ν : AdditiveHaarMeasure F)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (ℓ : glFunctionals ψ r π) (ℓ' : glInverseFunctionals ψ n σ) :
    dualUnequalRankRationalValuesAt hnr j k hr q ψ abv μ ν π σ ℓ ℓ' =
      unequalRankValuesAt k j (by omega) q (ψ.scale (-1)) abv μ
        (rectangularMeasure ν k (n + 1))
        (inverseTransposePullback π) (inverseTransposePullback σ)
        (firstDualFunctional ψ π ℓ) (secondDualFunctional ψ σ ℓ') := by
  rw [unequalRankValuesAt_eq_set]
  ext R
  constructor
  · rintro ⟨f, f', hR⟩
    exact ⟨translatedFirstDualModelEquiv ψ π ℓ (blockWeylAt n r hnr) f,
      secondDualModelMap ψ σ ℓ' f', hR⟩
  · rintro ⟨g, g', hR⟩
    obtain ⟨f, rfl⟩ :=
      (translatedFirstDualModelEquiv ψ π ℓ (blockWeylAt n r hnr)).surjective g
    obtain ⟨f', rfl⟩ := (secondDualModelMap_bijective ψ σ ℓ').surjective g'
    exact ⟨f, f', hR⟩

variable (j k : ℕ) (q : ℕ) (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
  (μ : Measure (LeftUnipotentQuotient n F)) (ν : AdditiveHaarMeasure F)
  (π : Representation ℂ (Langlands.GeneralLinear (n + (k + j + 1) + 1) F) V)
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
  (ℓ : glFunctionals ψ (n + (k + j + 1)) π) (ℓ' : glInverseFunctionals ψ n σ)

/-- Whittaker type and convergence identify the intrinsic dual values for block
`k,j` with the transformed values of the original block `j,k`. -/
theorem dualUnequalRankZetaValues_eq_rationalValues
    (hπ : IsOfWhittakerType (n + (k + j + 1))
      (standardCharacter (ψ.scale (-1)) (n + (k + j + 1))) (inverseTransposePullback π))
    (hσ : IsOfWhittakerType n (inverseStandardCharacter (ψ.scale (-1)) n)
      (inverseTransposePullback σ))
    (hℓ : ℓ.val ≠ 0) (hℓ' : ℓ'.val ≠ 0)
    (hconv : ∀ f : (coefficientModel (inverseTransposePullback π)
        (firstDualFunctional ψ π ℓ)).toSubmodule,
      ∀ f' : (coefficientModel (inverseTransposePullback σ)
        (secondDualFunctional ψ σ ℓ')).toSubmodule,
        ∃ a : ℝ, ∀ s : ℂ, a < s.re →
          UnequalRankConverges (ψ.scale (-1)) abv k j μ
            (rectangularMeasure ν k (n + 1)) f.val f'.val s) :
    dualUnequalRankZetaValues q ψ abv k j μ (rectangularMeasure ν k (n + 1)) π σ =
      dualUnequalRankRationalValuesAt (by omega) j k (by omega) q ψ abv μ ν π σ ℓ ℓ' := by
  rw [dualUnequalRankRationalValuesAt_eq]
  exact unequalRankZetaValues_eq_rationalValues q (ψ.scale (-1)) abv k j μ
    (rectangularMeasure ν k (n + 1)) hπ hσ
    (firstDualFunctional_ne_zero ψ π hℓ) (secondDualFunctional_ne_zero ψ σ hℓ') hconv

/-- A dual analytic conclusion gives the normalized-generator comparison for
swapped rectangular blocks in the unequal-rank functional equation. -/
theorem dualUnequalRank_isLPolynomial_iff
    (hπ : IsOfWhittakerType (n + (k + j + 1))
      (standardCharacter (ψ.scale (-1)) (n + (k + j + 1))) (inverseTransposePullback π))
    (hσ : IsOfWhittakerType n (inverseStandardCharacter (ψ.scale (-1)) n)
      (inverseTransposePullback σ))
    (hℓ : ℓ.val ≠ 0) (hℓ' : ℓ'.val ≠ 0)
    (h : UnequalRankAnalyticConclusion k j q (ψ.scale (-1)) abv μ
      (rectangularMeasure ν k (n + 1))
      (inverseTransposePullback π) (inverseTransposePullback σ)
      (firstDualFunctional ψ π ℓ) (secondDualFunctional ψ σ ℓ')) (P : ℂ[X]) :
    IsUnequalRankLPolynomial q (ψ.scale (-1)) abv k j μ
        (rectangularMeasure ν k (n + 1))
        (inverseTransposePullback π) (inverseTransposePullback σ) P ↔
      IsNormalizedGenerator (dualUnequalRankRationalValuesAt (by omega) j k (by omega)
        q ψ abv μ ν π σ ℓ ℓ') P := by
  rw [dualUnequalRankRationalValuesAt_eq]
  exact h.isUnequalRankLPolynomial_iff hπ hσ
    (firstDualFunctional_ne_zero ψ π hℓ) (secondDualFunctional_ne_zero ψ σ hℓ') P

end UnequalRank

end Langlands.RankinSelberg

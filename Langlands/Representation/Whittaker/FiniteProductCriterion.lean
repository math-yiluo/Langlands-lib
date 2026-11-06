import Langlands.Representation.Whittaker.TopDerivativeDual
import Langlands.Representation.Derivative.FiniteTopTensor

/-! # Full functional dual and nondegeneracy of finite normalized products -/

noncomputable section

namespace Langlands.Whittaker

open CategoryTheory GeneralLinear Derivative

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData)
  (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)

/-- The entire functional space of the actual finite normalized product is the
algebraic dual of the finite tensor of the entire original top derivatives. -/
def finiteProductFunctionalsDualEquiv {n : ℕ} (B : BlockShape n)
    (σ : letI := T.topology;
      ∀ i, SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier)) :
    letI := T.topology
    functionals (upperUnipotent n F.Carrier) (entrywiseCharacter ψ.complex n)
      ((T.normalizedProductInductionFunctor B).obj σ).representation ≃ₗ[ℂ]
        Module.Dual ℂ (PiTensorProduct ℂ (fun i =>
          (generalLinearDerivative T ψ (B.size i) (B.size i) le_rfl).obj (σ i))) := by
  letI := T.topology
  exact (functionalsTopDerivativeDualEquiv T ψ n
    ((T.normalizedProductInductionFunctor B).obj σ)).trans
      (finiteProductTopDerivativeTensorEquiv.{uF,uV} T ψ B σ).symm.dualMap

/-- A finite normalized product has a nonzero all-rank Whittaker functional
exactly when every one of its original factors does. -/
theorem hasFunctional_finiteProduct_iff {n : ℕ} (B : BlockShape n)
    (σ : letI := T.topology;
      ∀ i, SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier)) :
    letI := T.topology
    HasFunctional (N := upperUnipotent n F.Carrier)
      (θ := entrywiseCharacter ψ.complex n)
      ((T.normalizedProductInductionFunctor B).obj σ).representation ↔
        ∀ i, HasFunctional (N := upperUnipotent (B.size i) F.Carrier)
          (θ := entrywiseCharacter ψ.complex (B.size i)) (σ i).representation := by
  let := T.topology
  rw [hasFunctional_iff_nontrivial_topDerivative]
  exact (nontrivial_finiteProductTopDerivative_iff.{uF,uV} T ψ B σ).trans
    (forall_congr' (fun i =>
      (hasFunctional_iff_nontrivial_topDerivative T ψ (B.size i) (σ i)).symm))

/-- At positive ambient rank the source character is exactly the standard
character; the original factors retain their supplied block ranks. -/
theorem hasStandardFunctional_finiteProduct_iff (n : ℕ) (B : BlockShape (n + 1))
    (σ : letI := T.topology;
      ∀ i, SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier)) :
    letI := T.topology
    HasFunctional (N := upperUnipotent (n + 1) F.Carrier)
      (θ := standardCharacter ψ n)
      ((T.normalizedProductInductionFunctor B).obj σ).representation ↔
        ∀ i, HasFunctional (N := upperUnipotent (B.size i) F.Carrier)
          (θ := entrywiseCharacter ψ.complex (B.size i)) (σ i).representation := by
  let := T.topology
  rw [← entrywiseCharacter_eq_standardCharacter]
  exact hasFunctional_finiteProduct_iff.{uF,uV} T ψ B σ

end Langlands.Whittaker

import Langlands.Representation.GodementJacquet.ModelMatrixAnalyticData
import Langlands.Representation.GodementJacquet.CoefficientTransport
import Langlands.Representation.GodementJacquet.TwoBlockAnalyticAssembly
import Langlands.Representation.GodementJacquet.TwoBlockReverseRealization
import Langlands.Representation.RankinSelberg.InducedWhittakerQuotient
import Langlands.Representation.RankinSelberg.NormalizedProductWhittakerTypeProof
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonModels
import Langlands.Representation.RankinSelberg.RankOneTestReduction
import Langlands.Representation.RankinSelberg.LaurentDivisibilityProof

/-!
# L-divisibility through induction of the actual coefficient quotients

The uniform Mellin premise remains explicit. No functional equation is needed.
-/

noncomputable section

namespace Langlands.GodementJacquet

open MeasureTheory HarmonicAnalysis Whittaker RankinSelberg

universe uG uF uV uW

/-- A genuine quotient of a smooth representation has no additional
bi-smooth coefficient functions. -/
theorem biSmoothMatrixCoefficients_le_of_surjective
    {G : Type uG} [Group G] [TopologicalSpace G]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {τ : Representation ℂ G W}
    (hρ : IsSmooth ρ) (q : ρ.IntertwiningMap τ) (hq : Function.Surjective q) :
    biSmoothMatrixCoefficients τ ≤ biSmoothMatrixCoefficients ρ := by
  apply Submodule.span_le.mpr
  rintro f ⟨Λ, w, rfl⟩
  obtain ⟨v, hv⟩ := hq w.val
  let Λ' : SmoothDual ρ :=
    ⟨dualIntertwining q Λ.val, isSmoothVector_map (dualIntertwining q) Λ.property⟩
  refine Submodule.subset_span ⟨Λ', ⟨v, hρ v⟩, ?_⟩
  funext g
  change Λ.val (q (ρ g v)) = Λ.val (τ g w.val)
  rw [q.isIntertwining, hv]

/-- Inclusion of actual coefficient functions preserves the same test and
the same rational continuation in the matrix value set. -/
theorem matrixRationalValues_subset_of_coefficients_le
    {F : Type uF} [Field F] [TopologicalSpace F] {n : ℕ}
    [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (q : ℕ) (abv : AbsoluteValue F ℝ)
    (μ : Measure (Langlands.GeneralLinear (n + 1) F))
    {ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V}
    {τ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}
    (h : biSmoothMatrixCoefficients τ ≤ biSmoothMatrixCoefficients ρ) :
    matrixRationalValues q abv μ τ ⊆ matrixRationalValues q abv μ ρ := by
  rintro R ⟨Φ, f, hR⟩
  exact ⟨Φ, ⟨f.val, h f.property⟩, hR⟩

end Langlands.GodementJacquet

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear Polynomial

universe uF uV uW

section ModelInclusion

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance twoBlockModelLTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance twoBlockModelLGLMeasurable {n : ℕ} : MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  borel _

/-- The coefficient model of a full-type source is a genuine quotient of
any smooth quotient with a nonzero functional. Only the models are identified. -/
theorem model_jpssI2_le_of_surjective
    (ψ : UnitaryAdditiveCharacter F.Carrier) {n : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (τ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
    (hρ : IsOfWhittakerType n (standardCharacter ψ n) ρ)
    (hτ : IsSmooth τ) (q : ρ.IntertwiningMap τ) (hq : Function.Surjective q)
    (ℓ : glFunctionals ψ n ρ) (hℓ : ℓ.val ≠ 0)
    (ℓ' : glFunctionals ψ n τ) (hℓ' : ℓ'.val ≠ 0) :
    GodementJacquet.Padic.jpssI2 F
        (V := (glCoefficientModel ψ n ρ ℓ).toSubmodule)
        (glModelRepresentation ψ n ρ ℓ) ≤
      GodementJacquet.Padic.jpssI2 F τ := by
  let : AddCommGroup (glCoefficientModel ψ n ρ ℓ).toSubmodule :=
    (glCoefficientModel ψ n ρ ℓ).toSubmodule.addCommGroup
  let : AddCommGroup (glCoefficientModel ψ n τ ℓ').toSubmodule :=
    (glCoefficientModel ψ n τ ℓ').toSubmodule.addCommGroup
  have heq := coefficientModel_eq_of_surjective_of_whittakerType hρ q hq ℓ ℓ' hℓ hℓ'
  let e : (glModelRepresentation ψ n ρ ℓ).Equiv
      (glModelRepresentation ψ n τ ℓ') :=
    Representation.Equiv.mk
      (LinearEquiv.ofEq (glCoefficientModel ψ n ρ ℓ).toSubmodule
        (glCoefficientModel ψ n τ ℓ').toSubmodule
        (congrArg Subrepresentation.toSubmodule heq))
      (fun _ => by ext w; rfl)
  have hcoeff : GodementJacquet.biSmoothMatrixCoefficients
      (glModelRepresentation ψ n ρ ℓ) ≤ GodementJacquet.biSmoothMatrixCoefficients τ := by
    rw [GodementJacquet.biSmoothMatrixCoefficients_equiv e]
    exact GodementJacquet.biSmoothMatrixCoefficients_le_of_surjective hτ
      (modelMap τ ℓ') (modelMap_surjective τ ℓ')
  exact Submodule.span_mono
    (GodementJacquet.matrixRationalValues_subset_of_coefficients_le _ _ _ hcoeff)

end ModelInclusion

/-- Exchange the trivial scalar test with the other member, retaining the
entire symmetric certificate even in rank one. -/
theorem isPadicSymmetricLPolynomial_rankOne_one_swap
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
      AdditiveHaarMeasure F.Carrier)
    {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (P : Polynomial ℂ) :
    IsPadicSymmetricLPolynomial F ψ ν σ (rankOneCharacter 1) P ↔
      IsPadicSymmetricLPolynomial F ψ ν (rankOneCharacter 1) σ P := by
  cases n with
  | zero =>
    simp only [IsPadicSymmetricLPolynomial, Nat.le_refl, ite_true]
    exact isPadicPairLPolynomial_swap_equalRank F ψ ν σ (rankOneCharacter 1) P
  | succ n =>
    simp only [IsPadicSymmetricLPolynomial, Nat.zero_le,
      show ¬ n + 1 ≤ 0 by omega, ite_true, ite_false]

set_option maxHeartbeats 800000 in
/-- The full rank-one L base follows from the ordinary model analytics,
with the uniform Mellin convergence assertion still supplied explicitly. -/
theorem twoBlockLRankOne_of_uniform_mellin
    (hU : UniformFiniteFunctionMellinConvergenceStatement.{uF}) :
    TwoBlockLRankOneStatement.{uF,uV,uW} := by
  apply twoBlockLRankOne_of_trivial_test
  intro p hp F ψ ν t m h W hadd hmod σ hσ
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let : ∀ n : ℕ, MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) :=
    fun _ => borel _
  let : ∀ n : ℕ, BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) :=
    fun _ => ⟨rfl⟩
  choose ℓ hℓ using fun i => (hσ i).exists_ne_zero
  let M : Fin 2 → Type uF :=
    fun i => (glCoefficientModel ψ (m i) (σ i) (ℓ i)).toSubmodule
  let : ∀ i, AddCommGroup (M i) :=
    fun i => (glCoefficientModel ψ (m i) (σ i) (ℓ i)).toSubmodule.addCommGroup
  let : ∀ i, Module ℂ (M i) := fun i => inferInstance
  let τ (i : Fin 2) : Representation ℂ
      (Langlands.GeneralLinear (m i + 1) F.Carrier) (M i) :=
    glModelRepresentation ψ (m i) (σ i) (ℓ i)
  have hτ (i : Fin 2) : IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (τ i) :=
    glCoefficientModel_isOfWhittakerType F ψ (σ i) (hσ i) (ℓ i) (hℓ i)
  let Pi : Fin 2 → Polynomial ℂ :=
    fun i => GodementJacquet.Padic.modelMatrixLPolynomial F ψ (σ i) ν (hσ i)
  have hblock (i : Fin 2) : GodementJacquet.Padic.MatrixAnalyticAssertions F (τ i) (Pi i) :=
    GodementJacquet.Padic.modelMatrixAnalyticAssertions F ψ (σ i) hU ν (hσ i) (ℓ i) (hℓ i)
  let I := F.canonicalNormalizedProductInduced (succBlockShape m h) σ
  let J := F.canonicalNormalizedProductInduced (succBlockShape m h) τ
  have hI : IsOfWhittakerType t (standardCharacter ψ t) I :=
    normalizedProductWhittakerType p F ψ t 2 m h σ hσ
  have hJ : IsOfWhittakerType t (standardCharacter ψ t) J :=
    normalizedProductWhittakerType p F ψ t 2 m h τ hτ
  have hJan : GodementJacquet.Padic.MatrixAnalyticAssertions F J (∏ i, Pi i) :=
    GodementJacquet.matrixAnalyticAssertions_twoBlock_of_generators _
      F.canonicalTopologicalData.residueCardinality_gt_one _ _ _ m _ τ Pi hblock
      (GodementJacquet.TwoBlock.twoBlock_matrixGeneratorInputs F h τ
        (fun i => (hτ i).1.1) (fun i => (hτ i).1) Pi hblock)
  let q : I.IntertwiningMap J :=
    F.canonicalTopologicalData.normalizedProductModelMap (succBlockShape m h) σ ℓ
  have hq : Function.Surjective q :=
    F.canonicalTopologicalData.normalizedProductModelMap_surjective
      (succBlockShape m h) σ (fun i => (hσ i).1.1) ℓ
  obtain ⟨ℓI, hℓI⟩ := hI.exists_ne_zero
  obtain ⟨ℓJ, hℓJ⟩ := hJ.exists_ne_zero
  let P := GodementJacquet.Padic.modelMatrixLPolynomial F ψ I ν hI
  have hP := GodementJacquet.Padic.modelMatrixLPolynomial_pair F ψ I ν hI
  have hPgen := GodementJacquet.Padic.modelMatrixLPolynomial_normalized F ψ I ν hI ℓI hℓI
  have hle := model_jpssI2_le_of_surjective F ψ I J hI hJ.1.1 q hq ℓI hℓI ℓJ hℓJ
  have hdiv : P ∣ ∏ i, Pi i :=
    (normalizedGeneratorSpanDivisibility _ _ P (∏ i, Pi i) hPgen hJan.2.2).1 hle
  refine ⟨P, Pi, (isPadicSymmetricLPolynomial_rankOne_one_swap F ψ ν.val I P).1 hP,
    fun i => ?_, ?_⟩
  · exact (isPadicSymmetricLPolynomial_rankOne_one_swap F ψ ν.val (σ i) (Pi i)).1
      (GodementJacquet.Padic.modelMatrixLPolynomial_pair F ψ (σ i) ν (hσ i))
  · obtain ⟨Q, hQ⟩ := hdiv
    exact ⟨Q, 0, by rw [pow_zero, one_mul]; exact hQ.trans (mul_comm _ _)⟩

end Langlands.RankinSelberg

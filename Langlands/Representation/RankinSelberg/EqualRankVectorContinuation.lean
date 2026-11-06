import Langlands.Representation.RankinSelberg.EqualRankContinuationFamily
import Langlands.Representation.RankinSelberg.LaurentEvaluation
import Langlands.Representation.RankinSelberg.LaurentCentralBound
import Langlands.Representation.RankinSelberg.CentralSpectralElement
import Langlands.Representation.Smooth.Schur.Proof
import Langlands.HarmonicAnalysis.RowSchwartzAction

/-! # Equal-rank continuations on representation vectors and central recurrence -/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uV uW

section Family

variable {F : Type uF} [Field F] [TopologicalSpace F] {n : ℕ}
  [MeasurableSpace (LeftUnipotentQuotient n F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
  {μ : Measure (LeftUnipotentQuotient n F)}
  {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}
  {ℓ : glFunctionals ψ n π} {ℓ' : glInverseFunctionals ψ n σ}

/-- The actual equal-rank rational continuation pulled back along the canonical
coefficient maps, retaining the original representation vectors. -/
def equalRankVectorContinuation (hq : 1 < q)
    (hA : EqualRankAnalyticConclusion q ψ abv μ π σ ℓ ℓ') :
    V →ₗ[ℂ] W →ₗ[ℂ] SchwartzBruhat (Fin (n + 1) → F) →ₗ[ℂ] RationalFunctions :=
  trilinearPrecomp (equalRankContinuationFamily hq hA)
    (modelMap π ℓ).toLinearMap (modelMap σ ℓ').toLinearMap LinearMap.id

@[simp] theorem equalRankVectorContinuation_apply (hq : 1 < q)
    (hA : EqualRankAnalyticConclusion q ψ abv μ π σ ℓ ℓ')
    (v : V) (w : W) (Φ : SchwartzBruhat (Fin (n + 1) → F)) :
    equalRankVectorContinuation hq hA v w Φ =
      equalRankContinuationFamily hq hA (modelMap π ℓ v) (modelMap σ ℓ' w) Φ := rfl

/-- Its values are exactly the rational values of the two coefficient models. -/
theorem mem_equalRankRationalValues_iff_vector (hq : 1 < q)
    (hA : EqualRankAnalyticConclusion q ψ abv μ π σ ℓ ℓ') (R : RationalFunctions) :
    R ∈ equalRankRationalValues q ψ abv μ π σ ℓ ℓ' ↔
      ∃ v w Φ, equalRankVectorContinuation hq hA v w Φ = R := by
  constructor
  · rintro ⟨f, f', Φ, hR⟩
    obtain ⟨v, rfl⟩ := modelMap_surjective π ℓ f
    obtain ⟨w, rfl⟩ := modelMap_surjective σ ℓ' f'
    exact ⟨v, w, Φ, equalRankContinuationFamily_eq hq hA hR⟩
  · rintro ⟨v, w, Φ, rfl⟩
    exact ⟨modelMap π ℓ v, modelMap σ ℓ' w, Φ,
      equalRankContinuationFamily_spec hq hA _ _ _⟩

/-- The normalized generator clears every vector continuation value. -/
theorem equalRankVectorContinuation_clears (hq : 1 < q)
    (hA : EqualRankAnalyticConclusion q ψ abv μ π σ ℓ ℓ')
    {P : Polynomial ℂ}
    (hP : IsNormalizedGenerator (equalRankRationalValues q ψ abv μ π σ ℓ ℓ') P)
    (v : V) (w : W) (Φ : SchwartzBruhat (Fin (n + 1) → F)) :
    ∃ a : LaurentCoefficients, laurentToRatFunc a =
      algebraMap (Polynomial ℂ) RationalFunctions P * equalRankVectorContinuation hq hA v w Φ :=
  hP.clearsDenominators (mem_zetaSpan
    ((mem_equalRankRationalValues_iff_vector hq hA _).mpr ⟨v, w, Φ, rfl⟩))

variable [IsTopologicalRing F] [BorelSpace (LeftUnipotentQuotient n F)]

/-- The original-vector family satisfies the actual simultaneous translation law. -/
theorem equalRankVectorContinuation_translate (hq : 1 < q)
    (hA : EqualRankAnalyticConclusion q ψ abv μ π σ ℓ ℓ')
    (hμ : ∀ g, MeasurePreserving (rightTranslate (upperUnipotent (n + 1) F) g) μ μ)
    (g : Langlands.GeneralLinear (n + 1) F) (m : ℤ)
    (hg : abv (Matrix.det g.val) = (q : ℝ) ^ m)
    (v : V) (w : W) (Φ : SchwartzBruhat (Fin (n + 1) → F)) :
    equalRankVectorContinuation hq hA (π g v) (σ g w) (rowTranslate g Φ) =
      RatFunc.X ^ m * equalRankVectorContinuation hq hA v w Φ := by
  simp only [equalRankVectorContinuation_apply,
    (modelMap π ℓ).isIntertwining, (modelMap σ ℓ').isIntertwining]
  exact equalRankContinuationFamily_translate hq hA hμ g m hg _ _ (fun _ => rfl)

/-- Schur's central characters supply a nonzero scalar in the central recurrence
for actual integral continuations, at any central element of positive or zero
integral determinant exponent. -/
theorem equalRankVectorContinuation_centralShiftLaw
    [IsTopologicalGroup (Langlands.GeneralLinear (n + 1) F)]
    (hq : 1 < q) (hA : EqualRankAnalyticConclusion q ψ abv μ π σ ℓ ℓ')
    (hμ : ∀ g, MeasurePreserving (rightTranslate (upperUnipotent (n + 1) F) g) μ μ)
    (hπ : IsAdmissible π) (hiπ : π.IsIrreducible)
    (hσ : IsAdmissible σ) (hiσ : σ.IsIrreducible)
    (z : Subgroup.center (Langlands.GeneralLinear (n + 1) F)) (m : ℕ)
    (hz : abv (Matrix.det (z : Langlands.GeneralLinear (n + 1) F).val) = (q : ℝ) ^ m) :
    ∃ c : ℂ, c ≠ 0 ∧ CentralShiftLaw (equalRankVectorContinuation hq hA)
      (rowTranslate (z : Langlands.GeneralLinear (n + 1) F)).toLinearMap c m := by
  obtain ⟨χ, ⟨_, hχ⟩, _⟩ := admissibleSchur_centralCharacter π hπ hiπ
  obtain ⟨η, ⟨_, hη⟩, _⟩ := admissibleSchur_centralCharacter σ hσ hiσ
  refine ⟨(χ z : ℂ) * (η z : ℂ), mul_ne_zero (χ z).ne_zero (η z).ne_zero, ?_⟩
  intro v w Φ
  have ht := equalRankVectorContinuation_translate hq hA hμ (z : _) (m : ℤ)
    (by simpa only [zpow_natCast] using hz) v w Φ
  rw [hχ, hη] at ht
  simpa only [map_smul, LinearMap.smul_apply, RingHom.id_apply,
    smul_smul, zpow_natCast, mul_comm (η z : ℂ) (χ z : ℂ),
    LinearEquiv.coe_coe, LinearEquiv.coe_toLinearMap] using ht

end Family

/-- The actual inverse-uniformizer scalar gives a central recurrence of positive
degree equal to the common rank. -/
theorem equalRankVectorContinuation_inverseUniformizer
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel (LeftUnipotentQuotient n F.Carrier)
    ∀ {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {ψ : UnitaryAdditiveCharacter F.Carrier}
    {μ : Measure (LeftUnipotentQuotient n F.Carrier)}
    {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V}
    {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W}
    {ℓ : glFunctionals ψ n π} {ℓ' : glInverseFunctionals ψ n σ}
    (hA : EqualRankAnalyticConclusion T.residueCardinality ψ
      (normalizedAbsoluteValue T) μ π σ ℓ ℓ')
    (_hμ : ∀ g, MeasurePreserving
      (rightTranslate (upperUnipotent (n + 1) F.Carrier) g) μ μ)
    (_hπ : IsAdmissible π) (_hiπ : π.IsIrreducible)
    (_hσ : IsAdmissible σ) (_hiσ : σ.IsIrreducible),
    ∃ c : ℂ, c ≠ 0 ∧ CentralShiftLaw
      (equalRankVectorContinuation T.residueCardinality_gt_one hA)
      (rowTranslate (centralSpectralElement T (n + 1))).toLinearMap c (n + 1) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  intro V _ _ W _ _ ψ μ π σ ℓ ℓ' hA hμ hπ hiπ hσ hiσ
  exact equalRankVectorContinuation_centralShiftLaw
    T.residueCardinality_gt_one hA hμ hπ hiπ hσ hiσ
    ⟨centralSpectralElement T (n + 1), centralSpectralElement_mem_center T (n + 1)⟩
    (n + 1) (centralSpectralElement_det_abs T (n + 1))

end Langlands.RankinSelberg

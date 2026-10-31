import Langlands.Representation.RankinSelberg.TwoBlockOrdinaryJacquetFunctionalStatement
import Langlands.Representation.RankinSelberg.TwoBlockJacquetConvergenceProof
import Langlands.Representation.RankinSelberg.TwoBlockDeformationCell
import Langlands.Representation.RankinSelberg.TwoBlockDeformationNonvanishing

/-!
# Proof of the ordinary two-block Jacquet functional realization

Proof of `Langlands.RankinSelberg.TwoBlockOrdinaryJacquetFunctionalStatement`.
-/

noncomputable section

open MeasureTheory

namespace Langlands.RankinSelberg.TwoBlockOrdinaryJacquet

open HarmonicAnalysis Whittaker GeneralLinear TwoBlockJacquet TwoBlockDeformation

universe uF uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable [MeasurableSpace F.Carrier]
variable (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
variable (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i))
variable (ell : ∀ i, W i →ₗ[ℂ] ℂ)

/-- JPSS (4.6.2) at the identity, `f ↦ J(f)(1)`, as a linear functional on all sections,
when the integrand of every section is absolutely integrable at the identity. -/
def ordinaryJacquetFunctional
    (μ : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier))
    (hint : ∀ f : Sections F h σ, IsAbsIntegrableAt ψ ell μ f 1) :
    Sections F h σ →ₗ[ℂ] ℂ where
  toFun f := jacquetFunction ψ ell μ f 1
  map_add' f f' := jacquetFunction_add ψ ell μ (hint f) (hint f')
  map_smul' c f := jacquetFunction_smul ψ ell μ c f 1

theorem ordinaryJacquetFunctional_apply
    (μ : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier))
    (hint : ∀ f : Sections F h σ, IsAbsIntegrableAt ψ ell μ f 1) (f : Sections F h σ) :
    ordinaryJacquetFunctional F h ψ σ ell μ hint f = jacquetFunction ψ ell μ f 1 :=
  rfl

/-- The coefficient `g ↦ J(I(g) f)` of the functional is the ordinary integral `J(f)(g)`. -/
theorem ordinaryJacquetFunctional_inducedRep
    (μ : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier))
    (hint : ∀ f : Sections F h σ, IsAbsIntegrableAt ψ ell μ f 1)
    (g : GeneralLinear (t + 1) F.Carrier) (f : Sections F h σ) :
    ordinaryJacquetFunctional F h ψ σ ell μ hint (inducedRep F h σ g f) =
      jacquetFunction ψ ell μ f g := by
  rw [ordinaryJacquetFunctional_apply, jacquetFunction_inducedRep, one_mul]

/-- For block functionals equivariant for the inverse standard characters, the functional is
equivariant for the inverse standard character of `GL_(t+1)`. -/
theorem ordinaryJacquetFunctional_mem [MeasurableAdd₂ F.Carrier] [MeasurableMul F.Carrier]
    (hell : ∀ i, letI := F.canonicalTopologicalData.topology
      ell i ∈ glInverseFunctionals ψ (m i) (σ i)) :
    letI := F.canonicalTopologicalData.topology
    ∀ [BorelSpace (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier)]
      (μ : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier)) [μ.IsAddHaarMeasure]
      (hint : ∀ f : Sections F h σ, IsAbsIntegrableAt ψ ell μ f 1),
      ordinaryJacquetFunctional F h ψ σ ell μ hint ∈ glInverseFunctionals ψ t (inducedRep F h σ) := by
  let := F.canonicalTopologicalData.topology
  intro _ μ _ hint n f
  exact jacquetFunction_inducedRep_upperUnipotent F h σ ψ ell hell μ n f

/-- For smooth blocks and nonzero block functionals, the functional is nonzero. -/
theorem ordinaryJacquetFunctional_ne_zero
    (hσ : letI := F.canonicalTopologicalData.topology
      ∀ i, IsSmooth (σ i))
    (hell : ∀ i, ell i ≠ 0) :
    letI := F.canonicalTopologicalData.topology
    ∀ [BorelSpace (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier)]
      (μ : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier)) [μ.IsAddHaarMeasure]
      (hint : ∀ f : Sections F h σ, IsAbsIntegrableAt ψ ell μ f 1),
      ordinaryJacquetFunctional F h ψ σ ell μ hint ≠ 0 := by
  let := F.canonicalTopologicalData.topology
  intro _ μ _ hint h0
  obtain ⟨f, -, hf⟩ := exists_section_jacquetFunction_one_ne_zero F h ψ σ hσ ell hell μ
  apply hf
  rw [← ordinaryJacquetFunctional_apply F h ψ σ ell μ hint, h0, LinearMap.zero_apply]

end Langlands.RankinSelberg.TwoBlockOrdinaryJacquet

namespace Langlands.RankinSelberg

open HarmonicAnalysis Whittaker GeneralLinear TwoBlockJacquet TwoBlockDeformation
  TwoBlockOrdinaryJacquet

universe uF uW

/-- **JPSS 1983, Section (4.6).** For `u` above the ordinary convergence bound, the
ordinary two-block Jacquet integrals are the coefficients of one nonzero
inverse-character Whittaker functional on the actual lower induction. -/
theorem twoBlockOrdinaryJacquetFunctional :
    TwoBlockOrdinaryJacquetFunctionalStatement.{uF, uW} := by
  intro p _ F ψ ν t m h W _ _ τ hτ ell hell
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have : SecondCountableTopology F.Carrier := T.secondCountableTopology
  let : MeasurableSpace F.Carrier := borel F.Carrier
  have : BorelSpace F.Carrier := ⟨rfl⟩
  have : BorelSpace (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier) :=
    inferInstanceAs (BorelSpace (Fin (m 0 + 1) → Fin (m 1 + 1) → F.Carrier))
  obtain ⟨C, hC⟩ := twoBlockJacquetConvergence p F ψ ν t m h τ hτ ell hell
  refine ⟨C, fun u hu => ⟨hC u hu, ?_⟩⟩
  let σ := twoBlockOppositeTwistBlocks F m τ u
  let ell' : ∀ i, W i →ₗ[ℂ] ℂ := fun i => (ell i).val
  let μ := rectangularMeasure ν.val (m 0 + 1) (m 1 + 1)
  have hint : ∀ f : Sections F h σ, IsAbsIntegrableAt ψ ell' μ f 1 := fun f => hC u hu f 1
  have hmem : ∀ i, ell' i ∈ glInverseFunctionals ψ (m i) (σ i) :=
    fun i => (twoBlockOppositeTwistFunctional F m ψ τ u i (ell i)).property
  have hsmooth : ∀ i, IsSmooth (σ i) :=
    fun i => ((twoBlockOppositeTwistBlocks_isOfWhittakerType_iff F m τ u i _).mpr (hτ i)).1.1
  refine ⟨⟨ordinaryJacquetFunctional F h ψ σ ell' μ hint,
    ordinaryJacquetFunctional_mem F h ψ σ ell' hmem μ hint⟩,
    ordinaryJacquetFunctional_ne_zero F h ψ σ ell' hsmooth hell μ hint,
    fun f g => ordinaryJacquetFunctional_inducedRep F h ψ σ ell' μ hint g f⟩

end Langlands.RankinSelberg

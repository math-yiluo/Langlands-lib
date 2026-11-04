import Langlands.Representation.Plancherel.StandardIntertwiningIntegral

/-! # Measure normalization of the actual standard integral -/

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

namespace Langlands.HarmonicAnalysis.SmoothWeakIntegral

universe uX uG uV

variable {X : Type uX} [MeasurableSpace X]
  {G : Type uG} [Group G] [TopologicalSpace G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ G V} {μ : Measure X} {f : X → V} {v : V}

/-- Finite nonnegative rescaling of the measure rescales the actual weak
integral in the original carrier. -/
theorem HasIntegral.smul_measure_nnreal (hf : HasIntegral ρ μ f v) (c : ℝ≥0) :
    HasIntegral ρ (c • μ) f (((c : ℝ) : ℂ) • v) := by
  intro ℓ
  refine ⟨(hf ℓ).1.smul_measure_nnreal, ?_⟩
  rw [integral_smul_nnreal_measure, (hf ℓ).2, map_smul]
  rfl

/-- A positive finite measure rescaling preserves exactly the domain of
scalar convergence and representability. -/
theorem integrable_smul_measure_nnreal_iff (c : ℝ≥0) (hc : c ≠ 0) :
    Integrable ρ (c • μ) f ↔ Integrable ρ μ f := by
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨(((c⁻¹ : ℝ≥0) : ℝ) : ℂ) • v, ?_⟩
    simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using
      hv.smul_measure_nnreal c⁻¹
  · rintro ⟨v, hv⟩
    exact ⟨_, hv.smul_measure_nnreal c⟩

/-- A constant function has the total-mass multiple as representing vector
for every finite measure. -/
theorem hasIntegral_const [IsFiniteMeasure μ] (v : V) :
    HasIntegral ρ μ (fun _ : X => v) (((μ Set.univ).toReal : ℂ) • v) := by
  intro ℓ
  refine ⟨integrable_const _, ?_⟩
  rw [integral_const, map_smul]
  rfl

end Langlands.HarmonicAnalysis.SmoothWeakIntegral

namespace Langlands.Plancherel.StandardIntertwining

open Aubert.General Induction

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G} (h : IsSemidirectDecomposition P M U)
  (hU : IsClosed (U : Set G)) (U' : Subgroup G)
  (A : Langlands.SmoothRep.{0, uG, uV} ℂ M)
  [MeasurableSpace (QuotientSpace (U := U) U')]
  (ν : Measure (QuotientSpace (U := U) U'))

/-- Rescaling the quotient measure rescales every original scalar test and
its representing function. -/
theorem HasIntegral.smul_measure_nnreal
    {f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A}
    {Jf : G → A} (hf : HasIntegral h hU U' A ν f Jf) (c : ℝ≥0) :
    HasIntegral h hU U' A (c • ν) f (fun g => ((c : ℝ) : ℂ) • Jf g) :=
  fun g => (hf g).smul_measure_nnreal c

/-- The actual standard-integral domain is unchanged by positive finite
rescaling of its quotient measure. -/
theorem domain_smul_measure (c : ℝ≥0) (hc : c ≠ 0) :
    domain h hU U' A (c • ν) = domain h hU U' A ν := by
  ext f
  simp only [domain, Submodule.mem_iInf, Submodule.mem_comap,
    HarmonicAnalysis.SmoothWeakIntegral.mem_integrableSubmodule]
  exact forall_congr' fun _ =>
    HarmonicAnalysis.SmoothWeakIntegral.integrable_smul_measure_nnreal_iff c hc

/-- The selected operator changes by exactly the quotient-measure scalar. -/
theorem operator_smul_measure (hM : IsClosed (M : Set G))
    (c : ℝ≥0) (hc : c ≠ 0) (f : domain h hU U' A ν) :
    operator h hU U' A (c • ν) hM
        ⟨f.val, by rw [domain_smul_measure h hU U' A ν c hc]; exact f.property⟩ =
      fun g => ((c : ℝ) : ℂ) • operator h hU U' A ν hM f g :=
  operator_eq h hU U' A (c • ν) hM _
    (HasIntegral.smul_measure_nnreal h hU U' A ν
      (operator_spec h hU U' A ν hM f) c)

section Diagonal

/-- The actual diagonal quotient integrand is the constant source value. -/
theorem integrand_diagonal (g : G)
    (f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A) :
    integrand h hU U A g f =
      fun _ => eval P (leviInflatedInducingRepresentation h hU A) f g := by
  funext q
  induction q using Quotient.inductionOn with
  | h u =>
    rw [integrand_mk]
    exact source_unipotent_invariant h hU A f u g

variable [MeasurableSpace (QuotientSpace (U := U) U)]
  (ν₀ : Measure (QuotientSpace (U := U) U))

/-- For any finite diagonal quotient measure, every source function has the
total-mass multiple of its value as actual weak integral. -/
theorem hasIntegral_diagonal [IsFiniteMeasure ν₀]
    (f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A) :
    HasIntegral h hU U A ν₀ f
      (fun g => ((ν₀ Set.univ).toReal : ℂ) •
        eval P (leviInflatedInducingRepresentation h hU A) f g) := by
  intro g
  rw [integrand_diagonal]
  exact HarmonicAnalysis.SmoothWeakIntegral.hasIntegral_const _

/-- Finite diagonal quotient measures give the entire normalized induction
as the actual convergence and representability domain. -/
theorem domain_diagonal [IsFiniteMeasure ν₀] :
    domain h hU U A ν₀ = ⊤ := by
  apply top_unique
  intro f _
  exact (mem_domain h hU U A ν₀ f).mpr
    ⟨_, hasIntegral_diagonal h hU A ν₀ f⟩

/-- The selected diagonal operator is multiplication by the total mass. -/
theorem operator_diagonal [IsFiniteMeasure ν₀]
    (hM : IsClosed (M : Set G)) (f : domain h hU U A ν₀) :
    operator h hU U A ν₀ hM f =
      fun g => ((ν₀ Set.univ).toReal : ℂ) •
        eval P (leviInflatedInducingRepresentation h hU A) f.val g :=
  operator_eq h hU U A ν₀ hM f (hasIntegral_diagonal h hU A ν₀ f.val)

/-- A probability measure on the diagonal quotient gives the identity on
actual induced functions. -/
theorem operator_diagonal_probability [IsProbabilityMeasure ν₀]
    (hM : IsClosed (M : Set G)) (f : domain h hU U A ν₀) :
    operator h hU U A ν₀ hM f =
      fun g => eval P (leviInflatedInducingRepresentation h hU A) f.val g := by
  rw [operator_diagonal]
  simp only [measure_univ, ENNReal.toReal_one, Complex.ofReal_one, one_smul]

/-- The actual diagonal integral on the entire normalized induction, using
the proved convergence and representability of every input. -/
def diagonalOperator [IsFiniteMeasure ν₀] (hM : IsClosed (M : Set G)) :
    (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A →ₗ[ℂ] (G → A) :=
  (operator h hU U A ν₀ hM).comp
    ({ toFun f := ⟨f, (mem_domain h hU U A ν₀ f).mpr
        ⟨_, hasIntegral_diagonal h hU A ν₀ f⟩⟩
       map_add' _ _ := Subtype.ext rfl
       map_smul' _ _ := Subtype.ext rfl } :
      (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A →ₗ[ℂ]
        domain h hU U A ν₀)

/-- The full-source diagonal operator satisfies the original smooth-dual
scalar integral relation. -/
theorem diagonalOperator_spec [IsFiniteMeasure ν₀]
    (hM : IsClosed (M : Set G))
    (f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A) :
    HasIntegral h hU U A ν₀ f (diagonalOperator h hU A ν₀ hM f) :=
  operator_spec h hU U A ν₀ hM
    ⟨f, (mem_domain h hU U A ν₀ f).mpr ⟨_, hasIntegral_diagonal h hU A ν₀ f⟩⟩

/-- The full-source diagonal integral is the total-mass multiple of the
original induced function. -/
theorem diagonalOperator_eq [IsFiniteMeasure ν₀]
    (hM : IsClosed (M : Set G))
    (f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A) :
    diagonalOperator h hU A ν₀ hM f =
      fun g => ((ν₀ Set.univ).toReal : ℂ) •
        eval P (leviInflatedInducingRepresentation h hU A) f g :=
  operator_diagonal h hU A ν₀ hM
    ⟨f, (mem_domain h hU U A ν₀ f).mpr ⟨_, hasIntegral_diagonal h hU A ν₀ f⟩⟩

/-- With a probability diagonal quotient measure, the actual full-source
integral returns the original function. -/
theorem diagonalOperator_probability [IsProbabilityMeasure ν₀]
    (hM : IsClosed (M : Set G))
    (f : (DynamicNormalization.leviTwistedInductionFunctor h hU).obj A) :
    diagonalOperator h hU A ν₀ hM f =
      fun g => eval P (leviInflatedInducingRepresentation h hU A) f g :=
  operator_diagonal_probability h hU A ν₀ hM
    ⟨f, (mem_domain h hU U A ν₀ f).mpr ⟨_, hasIntegral_diagonal h hU A ν₀ f⟩⟩

end Diagonal

end Langlands.Plancherel.StandardIntertwining

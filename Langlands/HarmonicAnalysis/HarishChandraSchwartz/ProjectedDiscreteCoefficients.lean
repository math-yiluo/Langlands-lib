import Langlands.HarmonicAnalysis.HarishChandraSchwartz.SchwartzProjectedRepresentation
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.DiscreteCoefficientSpace
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.DiscreteSeriesCentralCoefficientSpace
import Langlands.Representation.Category.UniverseLift

/-! # Canonical discrete-series coefficients of projected function representations -/

noncomputable section

universe uG uV uW

open MeasureTheory Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz

section CanonicalCoefficients

variable {Γ : Type uG} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ Γ V}
  (A : Subgroup Γ) [A.Normal] (hA : A ≤ Subgroup.center Γ)
  [MeasurableSpace (Γ ⧸ A)] (mu : Measure (Γ ⧸ A)) [mu.IsHaarMeasure]

/-- The canonical discrete-series class of an actual irreducible square-integrable
subrepresentation, without a choice of an isomorphic representative. -/
def discreteSeriesClassOfSubrepresentation (hs : IsSmooth ρ) (S : Subrepresentation ρ)
    (hi : S.toRepresentation.IsIrreducible)
    (hsq : IsSquareIntegrableModCentralSubgroup A hA S.toRepresentation mu) :
    DiscreteSeriesClass.{uG, uV} A hA mu :=
  discreteSeriesClass A hA mu ⟨subrepresentationSmoothRep hs S, hi, hsq.1⟩ hsq

/-- Passing from an actual subrepresentation to its canonical class preserves
its whole coefficient space and the prescribed central action. -/
theorem coefficientFunctionSpace_subrepresentation_le (hs : IsSmooth ρ)
    (S : Subrepresentation ρ) (hi : S.toRepresentation.IsIrreducible)
    (hsq : IsSquareIntegrableModCentralSubgroup A hA S.toRepresentation mu)
    (χ : A →* ℂˣ)
    (hχ : ∀ (a : A) (v : S.toSubmodule), S.toRepresentation a v = (χ a : ℂ) • v) :
    coefficientFunctionSpace (subrepresentationSmoothRep hs S) ≤
      discreteSeriesCentralCoefficientSpace.{uG, uV} A hA mu χ := by
  let π : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := Γ) :=
    ⟨subrepresentationSmoothRep hs S, hi, hsq.1⟩
  let ω := discreteSeriesClass A hA mu π hsq
  have he : coefficientFunctionSpace (subrepresentationSmoothRep hs S) =
      coefficientFunctionSpace ω.val.out.obj :=
    coefficientFunctionSpace_eq_out_of_class_eq π ω.val rfl
  rw [he]
  exact coefficientFunctionSpace_le_discreteSeriesCentralCoefficientSpace
    A hA mu χ ω ((classActsByCharacter_mk A χ π).mpr hχ)

/-- The abstract unitary argument lands in the Library's canonical coefficient sum. -/
theorem coefficientFunctionSpace_le_discreteSeries_of_positiveForm
    (hcof : ∀ K : OpenSubgroup Γ, ∃ L : OpenSubgroup Γ, IsCompact (L : Set Γ) ∧ L ≤ K)
    (b : InvariantPositiveForm ρ) (ha : IsAdmissible ρ) (χ : A →* ℂˣ)
    (hχ : ∀ (a : A) (v : V), ρ a v = (χ a : ℂ) • v)
    (hL2 : ∀ e f : V, ∃ F : Γ ⧸ A → ℝ, MemLp F 2 mu ∧
      ∀ g : Γ, F (QuotientGroup.mk g) = ‖b.inner e (ρ g f)‖) :
    coefficientFunctionSpace (SmoothRep.of ρ ha.1) ≤
      discreteSeriesCentralCoefficientSpace.{uG, uV} A hA mu χ := by
  have hss : IsSemisimpleModule (MonoidAlgebra ℂ Γ) ρ.asModule :=
    (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρ).mp
      (admissibleUnitarySemisimplicity Γ hcof V ρ ha ⟨b⟩)
  have hcanonical : subrepresentationCoefficientSpace ha.1
      (fun S => S.toRepresentation.IsIrreducible) ≤
      (discreteSeriesCentralCoefficientSpace.{uG, uV} A hA mu χ).comap
        (LocallyConstant.coeFnₗ ℂ) := by
    refine iSup_le fun S => iSup_le fun hi => ?_
    intro f hf
    have hsquare := isSquareIntegrable_of_irreducible_subrepresentation
      A hA mu hcof b ha hL2 S hi
    apply coefficientFunctionSpace_subrepresentation_le A hA mu ha.1 S hi hsquare χ
      (fun a v => Subtype.ext (hχ a v))
    rw [coefficientFunctionSpace_eq_map]
    exact ⟨f, hf, rfl⟩
  refine iSup_le fun ℓ => ?_
  rintro _ ⟨v, rfl⟩
  exact hcanonical (smoothCoefficient_mem_irreducible ha.1 hss v ℓ)

/-- Lifting an actual irreducible admissible carrier preserves its coefficients,
square integrability and central action. -/
theorem coefficientFunctionSpace_le_lifted_discreteSeries
    (π : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := Γ))
    (hsq : IsSquareIntegrableModCentralSubgroup A hA π.obj.representation mu)
    (χ : A →* ℂˣ)
    (hχ : ∀ (a : A) (v : π.obj), π.obj.representation a v = (χ a : ℂ) • v) :
    coefficientFunctionSpace π.obj ≤
      discreteSeriesCentralCoefficientSpace.{uG, max uV uW} A hA mu χ := by
  let π' : IrreducibleAdmissibleRep.{0, uG, max uV uW} (k := ℂ) (G := Γ) :=
    ⟨SmoothRep.universeLift.{uW} π.obj,
      (SmoothRep.isIrreducible_universeLift_iff π.obj).mpr π.property.1,
      (SmoothRep.isAdmissible_universeLift_iff π.obj).mpr π.property.2⟩
  let e := SmoothRep.universeLiftEquiv.{uW} π.obj
  have hsq' : IsSquareIntegrableModCentralSubgroup A hA π'.obj.representation mu :=
    (isSquareIntegrableModCentralSubgroup_iff_of_equiv A hA e mu).mp hsq
  let ω := discreteSeriesClass A hA mu π' hsq'
  have hχ' : classActsByCharacter A χ ω.val :=
    (classActsByCharacter_mk A χ π').mpr (actsByCharacter_of_equiv e A χ hχ)
  calc
    coefficientFunctionSpace π.obj = coefficientFunctionSpace π'.obj :=
      coefficientFunctionSpace_eq_of_equiv e
    _ = coefficientFunctionSpace ω.val.out.obj :=
      coefficientFunctionSpace_eq_out_of_class_eq π' ω.val rfl
    _ ≤ discreteSeriesCentralCoefficientSpace.{uG, max uV uW} A hA mu χ :=
      coefficientFunctionSpace_le_discreteSeriesCentralCoefficientSpace A hA mu χ ω hχ'

/-- The canonical coefficient sum embeds into that with lifted representation
carriers, retaining an independent enlargement universe. -/
theorem discreteSeriesCentralCoefficientSpace_le_universeLift (χ : A →* ℂˣ) :
    discreteSeriesCentralCoefficientSpace.{uG, uV} A hA mu χ ≤
      discreteSeriesCentralCoefficientSpace.{uG, max uV uW} A hA mu χ := by
  refine iSup_le fun ω => ?_
  have hsq : IsSquareIntegrableModCentralSubgroup A hA
      ω.val.val.out.obj.representation mu := by
    change IsDiscreteSeriesClass A hA mu (Quotient.mk _ ω.val.val.out)
    exact (Quotient.out_eq ω.val.val).symm ▸ ω.val.property
  have hχ : ∀ (a : A) (v : ω.val.val.out.obj),
      ω.val.val.out.obj.representation a v = (χ a : ℂ) • v := by
    apply (classActsByCharacter_mk A χ ω.val.val.out).mp
    exact (Quotient.out_eq ω.val.val).symm ▸ ω.property
  exact coefficientFunctionSpace_le_lifted_discreteSeries A hA mu ω.val.val.out hsq χ hχ

end CanonicalCoefficients

section ProjectedEvaluation

variable {Γ : Type uG} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [Nonempty (CompactOpenSubgroup Γ)]
  {Ξ σ : Γ → ℝ} {A : Subgroup Γ} [MeasurableSpace A]
  (ht : TranslationWeights Ξ σ) (E : Submodule ℂ (Space Ξ σ))
  (hE : IsTranslationStable ht E) (hA : A ≤ Subgroup.center Γ)
  (muA : Measure A) (χ : A →* ℂˣ) (hc : CentralIntegralConvergesOn E muA χ)
  (H : OpenSubgroup Γ)

/-- Evaluation at one is a smooth functional on the actual projected left level:
the same open subgroup fixing functions on the left fixes the dual functional. -/
def projectedEvaluationAtOne : SmoothDual
    (projectedLeftSubrepresentation ht E hE hA muA χ H.toSubgroup).toRepresentation :=
  ⟨(LinearMap.proj 1).comp
    (projectedLeftSubrepresentation ht E hE hA muA χ H.toSubgroup).toSubmodule.subtype,
    H, by
      intro h
      apply LinearMap.ext
      intro f
      change (f : Γ → ℂ) (1 * (h : Γ)⁻¹) = (f : Γ → ℂ) 1
      have hf := isLeftInvariant_projectedLeftSubrepresentation
        ht E hE hA muA χ hc H.toSubgroup f
      simpa only [one_mul, mul_one] using hf _ (H.inv_mem h.property) 1⟩

/-- Every actual projected function is its own matrix coefficient against the
smooth evaluation functional. No supplied reproducing vector is needed. -/
theorem matrixCoefficient_projectedEvaluationAtOne
    (f : (projectedLeftSubrepresentation ht E hE hA muA χ H.toSubgroup).toSubmodule) :
    matrixCoefficient
      (projectedLeftSubrepresentation ht E hE hA muA χ H.toSubgroup).toRepresentation
      (projectedEvaluationAtOne ht E hE hA muA χ hc H).val f = (f : Γ → ℂ) := by
  funext g
  change (f : Γ → ℂ) (1 * g) = (f : Γ → ℂ) g
  rw [one_mul]

include hc in
/-- The remaining positive-form and coefficient-L² inputs imply the canonical
discrete-series conclusion for each vector of the actual projected representation. -/
theorem projected_mem_discreteSeries_of_positiveForm
    [A.Normal] [MeasurableMul A] [muA.IsMulRightInvariant]
    [MeasurableSpace (Γ ⧸ A)] (mu : Measure (Γ ⧸ A)) [mu.IsHaarMeasure]
    (hcof : ∀ K : OpenSubgroup Γ, ∃ L : OpenSubgroup Γ, IsCompact (L : Set Γ) ∧ L ≤ K)
    (b : InvariantPositiveForm
      (projectedLeftSubrepresentation ht E hE hA muA χ H.toSubgroup).toRepresentation)
    (ha : IsAdmissible
      (projectedLeftSubrepresentation ht E hE hA muA χ H.toSubgroup).toRepresentation)
    (hL2 : ∀ e f :
        (projectedLeftSubrepresentation ht E hE hA muA χ H.toSubgroup).toSubmodule,
      ∃ F : Γ ⧸ A → ℝ, MemLp F 2 mu ∧ ∀ g : Γ,
        F (QuotientGroup.mk g) =
          ‖b.inner e
            ((projectedLeftSubrepresentation ht E hE hA muA χ H.toSubgroup).toRepresentation
              g f)‖)
    (f : (projectedLeftSubrepresentation ht E hE hA muA χ H.toSubgroup).toSubmodule) :
    (f : Γ → ℂ) ∈ discreteSeriesCentralCoefficientSpace.{uG, uG} A hA mu χ := by
  rw [← matrixCoefficient_projectedEvaluationAtOne ht E hE hA muA χ hc H f]
  exact coefficientFunctionSpace_le_discreteSeries_of_positiveForm A hA mu hcof b ha χ
    (projectedLeftSubrepresentation_central ht E hE hA muA χ hc H.toSubgroup) hL2
    (matrixCoefficient_mem_coefficientFunctionSpace (SmoothRep.of _ ha.1)
      (projectedEvaluationAtOne ht E hE hA muA χ hc H) f)

include hc in
/-- The same conclusion in the enlarged carrier universe used by the full
VIII.4.2 equality, with independent group and enlargement universes. -/
theorem projected_mem_lifted_discreteSeries_of_positiveForm
    [A.Normal] [MeasurableMul A] [muA.IsMulRightInvariant]
    [MeasurableSpace (Γ ⧸ A)] (mu : Measure (Γ ⧸ A)) [mu.IsHaarMeasure]
    (hcof : ∀ K : OpenSubgroup Γ, ∃ L : OpenSubgroup Γ, IsCompact (L : Set Γ) ∧ L ≤ K)
    (b : InvariantPositiveForm
      (projectedLeftSubrepresentation ht E hE hA muA χ H.toSubgroup).toRepresentation)
    (ha : IsAdmissible
      (projectedLeftSubrepresentation ht E hE hA muA χ H.toSubgroup).toRepresentation)
    (hL2 : ∀ e f :
        (projectedLeftSubrepresentation ht E hE hA muA χ H.toSubgroup).toSubmodule,
      ∃ F : Γ ⧸ A → ℝ, MemLp F 2 mu ∧ ∀ g : Γ,
        F (QuotientGroup.mk g) =
          ‖b.inner e
            ((projectedLeftSubrepresentation ht E hE hA muA χ H.toSubgroup).toRepresentation
              g f)‖)
    (f : (projectedLeftSubrepresentation ht E hE hA muA χ H.toSubgroup).toSubmodule) :
    (f : Γ → ℂ) ∈ discreteSeriesCentralCoefficientSpace.{uG, max uG uW} A hA mu χ :=
  discreteSeriesCentralCoefficientSpace_le_universeLift A hA mu χ
    (projected_mem_discreteSeries_of_positiveForm ht E hE hA muA χ hc H mu hcof b ha hL2 f)

end ProjectedEvaluation

end Langlands.HarishChandraSchwartz

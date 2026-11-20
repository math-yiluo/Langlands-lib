import Langlands.BaseChange.SplitMatchingStatement
import Langlands.BaseChange.SplitMatchingQuotient
import Langlands.BaseChange.SplitMatchingOrbit
import Langlands.BaseChange.SplitMatchingConvolution

/-! Matching split tensors and convolution products at a split place. -/

noncomputable section

open MeasureTheory Topology
open scoped BigOperators

namespace Langlands.BaseChange

open HarmonicAnalysis (SchwartzBruhat)
open JacquetLanglands QuotientIntegration TraceFormula

universe u

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

section AssociatedPair

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {n l : ℕ}
  [MeasurableSpace (GeneralLinear n F)] [BorelSpace (GeneralLinear n F)]
  [MeasurableSpace (GeneralLinear n (Fin (l + 1) → F))]
  [BorelSpace (GeneralLinear n (Fin (l + 1) → F))]

local notation "G" => GeneralLinear n F
local notation "GE" => GeneralLinear n (Fin (l + 1) → F)
local notation "σ" => splitCyclicShift F (l + 1)
local notation "τ" => entrywiseAut σ n
local notation "κ" => splitGLCoordinates F n (l + 1)

private theorem splitConcordAt (μF : Measure G) [μF.IsHaarMeasure]
    (μE : Measure GE) [μE.IsHaarMeasure] (hμ : IsSplitProductHaar μF μE)
    (ψ : Fin (l + 1) → SchwartzBruhat G) (δ : GE) (γ : G)
    (hreg : IsRegularSemisimple γ) :
    ConcordAt σ (l + 1) μF μE
      (splitTensor fun i => (ψ i : G → ℂ)) (convolutionProduct μF ψ : G → ℂ) δ γ := by
  intro μδ _ _ μγ _ _ νδ νγ hνδ hνγ hassoc
  obtain ⟨a, ha, hmeas⟩ := hassoc
  let b := κ a 0
  have hγ : b⁻¹ * (List.ofFn (κ δ)).prod * b = γ :=
    splitAssociatedNorm_coordinate δ γ a ha
  let Θ := splitQuotientChart δ b γ hγ
  let ρ : Measure (Fin l → G) := Measure.pi fun _ => μF
  let φ := splitTensor fun i => (ψ i : G → ℂ)
  let f (p : LeftQuotient (glCentralizer γ) × (Fin l → G)) : ℂ :=
    ∏ i, ψ i (splitProductFiberChart l (regularOrbitMap γ p.1, p.2) i)
  let := LocalFieldTopology.t2Space F
  let := LocalFieldTopology.generalLinear_t2Space F n
  let := LocalFieldTopology.generalLinear_locallyCompactSpace F n
  let := LocalFieldTopology.generalLinear_secondCountableTopology F n
  let := leftQuotient_locallyCompactSpace (glCentralizer γ)
  let := (leftQuotient_isOpenQuotientMap (glCentralizer γ)).secondCountableTopology
  let : νγ.Regular := hνγ.regular
  have hΘ : MeasurePreserving Θ.symm (νγ.prod ρ) νδ :=
    splitQuotientChart_symm_measurePreserving δ b γ hγ hμ hνδ hνγ
      (splitCentralizerEquiv_measurePreserving δ γ a hγ μδ μγ hmeas)
  have hdesc (q : LeftQuotient (sigmaCentralizer σ n δ)) :
      twistedOrbitFunction τ δ φ q = f (Θ q) := by
    induction q using Quotient.inductionOn with
    | h x =>
      change φ (twistedConj τ x δ) =
        f (splitQuotientChart δ b γ hγ (leftQuotientMap (sigmaCentralizer σ n δ) x))
      rw [splitQuotientChart_mk]
      simp only [φ, f, regularOrbitMap_mk, splitProductFiberChart_apply,
        splitTensor_apply, ← splitGLCoordinates_apply, splitAmbientChart_twistedConj δ b γ hγ x]
  have hj : IsClosedEmbedding (fun p : LeftQuotient (glCentralizer γ) × (Fin l → G) =>
      (regularOrbitMap γ p.1, p.2)) :=
    (regularOrbitMap_isClosedEmbedding γ hreg).prodMap IsClosedEmbedding.id
  have hf : Integrable f (νγ.prod ρ) := splitProductFiber_integrable hj _ ψ
  change (∫ q, twistedOrbitFunction τ δ φ q ∂νδ) = _
  calc
    _ = ∫ p, twistedOrbitFunction τ δ φ (Θ.symm p) ∂νγ.prod ρ :=
      (hΘ.integral_comp Θ.symm.toMeasurableEquiv.measurableEmbedding
        (twistedOrbitFunction τ δ φ)).symm
    _ = ∫ p, f p ∂νγ.prod ρ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun p => by
        change twistedOrbitFunction τ δ φ (Θ.symm p) = f p
        rw [hdesc, Homeomorph.apply_symm_apply]
    _ = ∫ q, ∫ w, f (q, w) ∂ρ ∂νγ := integral_prod f hf
    _ = ∫ q, convolutionProduct μF ψ (regularOrbitMap γ q) ∂νγ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun q => by
        change (∫ w, ∏ i, ψ i (splitProductFiberChart l (regularOrbitMap γ q, w) i)
          ∂Measure.pi (fun _ : Fin l => μF)) = _
        exact integral_splitProductFiber μF ψ (regularOrbitMap γ q)
    _ = orbitalIntegral γ νγ (convolutionProduct μF ψ : G → ℂ) := by
      unfold orbitalIntegral twistedOrbitalIntegral
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun q => by
        induction q using Quotient.inductionOn with
        | h x => rfl

end AssociatedPair

/-- Split tensors and the corresponding convolution products are concordant for product Haar
measure, and such a Haar measure exists. -/
theorem splitMatching : SplitMatchingStatement.{u} := by
  intro F _ _ _ _ n l
  let : MeasurableSpace (GeneralLinear n F) := borel _
  let : MeasurableSpace (GeneralLinear n (Fin (l + 1) → F)) := borel _
  let : BorelSpace (GeneralLinear n F) := ⟨rfl⟩
  let : BorelSpace (GeneralLinear n (Fin (l + 1) → F)) := ⟨rfl⟩
  intro μF _
  refine ⟨⟨splitProductMeasure μF, splitProductMeasure_isHaar μF,
    splitProductMeasure_isSplitProductHaar μF⟩, ?_⟩
  intro μE hE hμ ψ
  let : μE.IsHaarMeasure := hE
  constructor
  · intro γ _ hγ
    exact (hγ (isNorm_splitCyclicShift γ)).elim
  · intro δ γ _ hγ
    exact splitConcordAt μF μE hμ ψ δ γ hγ

end Langlands.BaseChange

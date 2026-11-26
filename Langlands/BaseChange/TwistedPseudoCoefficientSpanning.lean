import Langlands.BaseChange.TwistedCharacter.StandardTraceMembership
import Langlands.BaseChange.SigmaLiftTransport
import Langlands.BaseChange.TwistedPseudoCoefficientOrbitSeparation
import Langlands.LocalField.FiniteExtensionModuleTopology
import Langlands.Representation.Category.UniverseLift

/-! # Spanning the twisted irreducible spectrum by orbit, tempered and proper traces -/

noncomputable section

namespace Langlands.BaseChange

open GeneralLinear HarmonicAnalysis MeasureTheory PadicField.TopologicalData

universe u v z

section Padic

variable {F : Type u} [Field F] [TopologicalSpace F] {p : ℕ} [Fact p.Prime]
  {E : PadicField.{v} p} [Algebra F E.Carrier] (T : E.TopologicalData)
  (hModule : letI := T.topology; IsModuleTopology F E.Carrier)
  (σ : E.Carrier ≃ₐ[F] E.Carrier) {n : ℕ}

set_option maxHeartbeats 1200000 in
/-- Stable standard traces give spanning by the orbit, other essentially
tempered traces, and proper induced traces, with the carrier universe free. -/
theorem twistedSpectrumSpan_le_orbit_sup_tempered_sup_proper_padic (hn : 0 < n) :
    letI := T.topology
    letI := T.localField
    letI := T.valuativeRel
    letI := hModule
    ∀ [T2Space (GeneralLinear n E.Carrier)]
      [LocallyCompactSpace (GeneralLinear n E.Carrier)]
      [TotallyDisconnectedSpace (GeneralLinear n E.Carrier)]
      [MeasurableSpace (GeneralLinear n E.Carrier)] [BorelSpace (GeneralLinear n E.Carrier)]
      (μ : Measure (GeneralLinear n E.Carrier)) [IsFiniteMeasureOnCompacts μ]
      [μ.IsMulLeftInvariant]
      (W : Type z) [AddCommGroup W] [Module ℂ W]
      (τ : Representation ℂ (GeneralLinear n E.Carrier) W),
        let θ := entrywiseAut σ n
        twistedSpectrumSpan.{v,z} μ θ (fun _ _ _ _ => True) ≤
          twistedOrbitSpan μ θ τ ⊔ twistedOtherEssentiallyTemperedSpan μ θ τ ⊔
            sigmaProperInducedSpan.{u,v,z} σ μ := by
  let := T.topology
  let := T.localField
  let := T.valuativeRel
  let := hModule
  intro _ _ _ _ _ μ _ _ W _ _ τ
  let G := GeneralLinear n E.Carrier
  let θ := entrywiseAut σ n
  let L := twistedOrbitSpan μ θ τ ⊔ twistedOtherEssentiallyTemperedSpan μ θ τ ⊔
    sigmaProperInducedSpan.{u,v,z} σ μ
  let : SecondCountableTopology G := T.generalLinearSecondCountableTopology n
  have hStandard (t : T.TemperedLanglandsDatum.{max v z} n)
      (A : ∀ i, SigmaIntertwiner σ (t.shape.size i) (t.blocks i).representation) :
      twistedDistribution μ t.standardModule.representation (temperedStandard_isAdmissible T t)
        (temperedStandardSigmaIntertwiner T hModule σ t A).toLinearMap ∈ L := by
    by_cases ht : 2 ≤ t.shape.length
    · exact (le_sup_right : sigmaProperInducedSpan.{u,v,z} σ μ ≤ L)
        (temperedStandardTrace_mem_sigmaProperInducedSpan T hModule σ t ht μ A)
    have hpos : t.shape.length ≠ 0 := by
      intro h0
      have : IsEmpty (Fin t.shape.length) := Fin.isEmpty_iff.mpr h0
      have hsum := t.shape.sum_eq
      rw [Finset.sum_of_isEmpty] at hsum
      omega
    have hone : t.shape.length = 1 := by omega
    obtain ⟨hBirr, ψ, hψ, hψσ, htemp⟩ :=
      singleBlockStandard_irreducible_essentiallyTempered T hModule σ t hone
    let B := t.standardModule
    let S := temperedStandardSigmaIntertwiner T hModule σ t A
    let hB := temperedStandard_isAdmissible T t
    obtain ⟨R, hRirr, ⟨e⟩⟩ := exists_irreducible_smoothRep_equiv_of_separable.{v,max v z,z}
      B hBirr
    let hR := isAdmissible_of_equiv e hB
    let AR := SigmaIntertwiner.transport (σ := σ) S e
    have he : twistedDistribution μ B.representation hB S.toLinearMap =
        twistedDistribution μ R.representation hR AR.toLinearMap :=
      (twistedDistribution_eq_of_equivalent μ hB hR e S.toLinearMap).symm
    change twistedDistribution μ B.representation hB S.toLinearMap ∈ L
    rw [he]
    by_cases ho : IsUnramifiedTwistOf θ τ R.representation
    · apply (le_sup_left.trans le_sup_left : twistedOrbitSpan μ θ τ ≤ L)
      exact twistedDistribution_mem_twistedSpectrumSpan μ θ _ hR hRirr ho AR
    · apply (le_sup_right.trans le_sup_left : twistedOtherEssentiallyTemperedSpan μ θ τ ≤ L)
      have htempR := (isTemperedRep_iff_of_equiv (twistEquiv ψ e)).mp htemp
      exact twistedDistribution_mem_twistedSpectrumSpan μ θ _ hR hRirr
        ⟨ho, ψ, hψ, hψσ, htempR⟩ AR
  change twistedSpectrumSpan.{v,z} μ θ (fun _ _ _ _ => True) ≤ L
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨X, iAdd, iMod, ρ, hρ, A, hi, _, rfl⟩
  let := iAdd
  let := iMod
  let R := SmoothRep.of ρ hρ.1
  let B := R.universeLift.{v}
  let e := R.universeLiftEquiv.{v}
  let hB := isAdmissible_of_equiv e hρ
  let AB := SigmaIntertwiner.transport (σ := σ) A e
  have hBi : B.IsIrreducible := (isIrreducible_iff_of_equiv e).mp hi
  have hBmem := stableLanglandsTraceSpan.{u,v,z} F p E T hModule σ n hn μ L hStandard B hB hBi AB
  exact (twistedDistribution_eq_of_equivalent μ hρ hB e A.toLinearMap) ▸ hBmem

end Padic

/-- The spanning part of twisted pseudo-coefficient spectral splitting, before
adjoining any compact-level invisible classes. -/
def TwistedPseudoCoefficientSpanningStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (E : Type v) [Field E] [Algebra F E] [TopologicalSpace E]
    [IsTopologicalRing E] [IsModuleTopology F E] (σ : E ≃ₐ[F] E) (l n : ℕ),
    (hE : IsCyclicAlgebra σ l) → 0 < n →
    haveI : Module.Finite F E := hE.1
    letI : MeasurableSpace (GeneralLinear n E) := borel _
    haveI : BorelSpace (GeneralLinear n E) := ⟨rfl⟩
    haveI := generalLinear_t2Space_of_finite F E n
    haveI := generalLinear_locallyCompactSpace_of_finite F E n
    haveI := generalLinear_totallyDisconnectedSpace_of_finite F E n
    ∀ (W : Type z) [AddCommGroup W] [Module ℂ W]
      (τ : Representation ℂ (GeneralLinear n E) W)
      (μ : Measure (GeneralLinear n E)) [μ.IsHaarMeasure],
        let θ := entrywiseAut σ n
        twistedSpectrumSpan.{v,z} μ θ (fun _ _ _ _ => True) ≤
          twistedOrbitSpan μ θ τ ⊔ twistedOtherEssentiallyTemperedSpan μ θ τ ⊔
            sigmaProperInducedSpan.{u,v,z} σ μ

/-- Transfer the p-adic spanning result to the original extension field and
its supplied module topology. -/
theorem twistedPseudoCoefficientSpanning : TwistedPseudoCoefficientSpanningStatement.{u,v,z} := by
  intro F _ _ _ _ _ E _ _ _ _ _ σ l n hE hn
  let : Module.Finite F E := hE.1
  let : MeasurableSpace (GeneralLinear n E) := borel _
  let : BorelSpace (GeneralLinear n E) := ⟨rfl⟩
  let := generalLinear_t2Space_of_finite F E n
  let := generalLinear_locallyCompactSpace_of_finite F E n
  let := generalLinear_totallyDisconnectedSpace_of_finite F E n
  let := LocalField.FiniteExtension.valuativeRel F E
  let := LocalField.FiniteExtension.isLocalField_of_isModuleTopology F E
  let : CharZero E := charZero_of_injective_algebraMap (algebraMap F E).injective
  let T := CharZeroLocalField.topologicalData E
  let : Algebra F (CharZeroLocalField.padicField E).Carrier := ‹Algebra F E›
  intro W _ _ τ μ _
  exact @twistedSpectrumSpan_le_orbit_sup_tempered_sup_proper_padic.{u,v,z}
    F _ _ (CharZeroLocalField.residueChar E) _ (CharZeroLocalField.padicField E) _ T
    (inferInstanceAs (IsModuleTopology F E)) σ n hn
    (inferInstanceAs (T2Space (GeneralLinear n E)))
    (inferInstanceAs (LocallyCompactSpace (GeneralLinear n E)))
    (inferInstanceAs (TotallyDisconnectedSpace (GeneralLinear n E)))
    (inferInstanceAs (MeasurableSpace (GeneralLinear n E)))
    (inferInstanceAs (BorelSpace (GeneralLinear n E))) μ
    (inferInstanceAs (IsFiniteMeasureOnCompacts μ)) (inferInstanceAs μ.IsMulLeftInvariant)
    W _ _ τ

end Langlands.BaseChange

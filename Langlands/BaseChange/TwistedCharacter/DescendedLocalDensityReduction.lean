import Langlands.BaseChange.TwistedCharacter.CyclicSemisimpleDescent
import Langlands.BaseChange.TwistedCharacter.SemisimpleDensityRecovery
import Langlands.BaseChange.TwistedCharacter.SemisimpleDensityReduction

/-! # Twisted character integrability from a density on the descended slice -/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory MeasureTheory.Measure HarmonicAnalysis Set Function _root_.Topology
open scoped SemidirectProduct

/-- The local analytic assertion about the actual descended character distributions at zero. -/
def CyclicGLDescendedLocalDensityStatement.{u, v, w} : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (E : Type v) [CommRing E] [Algebra F E] [TopologicalSpace E]
    [IsTopologicalRing E] [IsModuleTopology F E] (σ : E ≃ₐ[F] E) (l n : ℕ)
    (hE : IsCyclicAlgebra σ l),
    haveI : NeZero l := ⟨hE.pos.ne'⟩
    haveI : Module.Finite F E := hE.1
    haveI := generalLinear_t2Space_of_finite F E n
    haveI := generalLinear_locallyCompactSpace_of_finite F E n
    haveI := generalLinear_totallyDisconnectedSpace_of_finite F E n
    haveI := cyclicGLSemidirect_isTopologicalGroup σ hE.pow_eq_one n
    let Mat := Matrix (Fin n) (Fin n) E
    let G := GeneralLinear n E
    let H := CyclicGLSemidirect σ hE.pow_eq_one n
    letI : NontriviallyNormedField F := LocalGalois.localNormedField F
    letI : ProperSpace F := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
    letI : IsModuleTopology F Mat := inferInstanceAs (IsModuleTopology F (Fin n → Fin n → E))
    letI : NormedRing Mat := finiteAlgebraNormedRing F Mat
    letI : NormedAlgebra F Mat := finiteAlgebraNormedAlgebra F Mat
    letI : CompleteSpace Mat := FiniteDimensional.complete F Mat
    letI : MeasurableSpace G := borel G
    haveI : BorelSpace G := ⟨rfl⟩
    letI : MeasurableSpace H := borel H
    haveI : BorelSpace H := ⟨rfl⟩
    ∀ {W : Type w} [AddCommGroup W] [Module ℂ W]
      (π : Representation ℂ H W) (hπ : IsAdmissible π), π.IsIrreducible →
      ∀ (s : H), IsCyclicGLSemisimple s → ∀ (ν : Measure H) [ν.IsHaarMeasure],
        let α := cyclicAdjointAlgEquiv s
        let S := adjointFixedAlgebra α
        let U := adjointConjugationDomain α
        let i : G →* H := SemidirectProduct.inl
        let hi : IsOpenEmbedding i := SemidirectProduct.isOpenEmbedding_inl _
        let μ := ν.comap (translatedCosetEmbedding i s)
        let D := translatedCosetDistribution i hi s (Character.distribution ν π hπ)
        letI : MeasurableSpace S := borel S
        ∀ (ρ : AdditiveHaarMeasure S) (P : SchwartzBruhat (G × U) →ₗ[ℂ] SchwartzBruhat G)
          (T : Distribution U) (T₀ : Distribution S) (C : Set S),
          IsClopen C → 0 ∈ C → C ⊆ U →
          SchwartzBruhat.IsTestPushforward (μ.prod (ρ.measure.comap Subtype.val)) μ
            (adjointConjugationOnUnits α) P →
          (letI : IsFiniteMeasureOnCompacts μ :=
              IsFiniteMeasureOnCompacts.comap' ν (isOpenEmbedding_translatedCoset i hi s).continuous
                (isOpenEmbedding_translatedCoset i hi s).measurableEmbedding
           D.comp P = Distribution.tensor (Distribution.ofMeasure μ) T) →
          UnitConjugation.IsConjugationInvariant T₀ → T₀ ∈ Distribution.supportedOn C →
          (∀ f : SchwartzBruhat U, support (f : U → ℂ) ⊆ Subtype.val ⁻¹' C →
            T₀ (SchwartzBruhat.extendZero (isOpen_adjointConjugationDomain α) f) = T f) →
          ∃ V : Set S, IsOpen V ∧ 0 ∈ V ∧ ∃ θ : S → ℂ,
            LocallyIntegrableOn θ V ρ.measure ∧ ∀ f : SchwartzBruhat S,
              support (f : S → ℂ) ⊆ V → T₀ f = ∫ y, θ y * f y ∂ρ.measure

/-- The full twisted integrability statement follows from the local summability of the
descended distributions at zero. -/
def TwistedCharacterFromDescendedLocalDensityStatement.{u, v, w} : Prop :=
  CyclicGLDescendedLocalDensityStatement.{u, v, w} →
    TwistedCharacterLocalIntegrabilityStatement.{u, v, w}

/-- Descent and recovery supply the local densities at the semisimple points of the cyclic
extension. The regular-value and globalization arguments then give the twisted statement. -/
theorem twistedCharacterFromDescendedLocalDensity.{u, v, w} :
    TwistedCharacterFromDescendedLocalDensityStatement.{u, v, w} := by
  intro hDensity
  apply twistedCharacterFromSemisimpleDensity
  intro F _ _ _ _ _ E _ _ _ _ _ σ l n hE H
  let : NeZero l := ⟨hE.pos.ne'⟩
  let : Module.Finite F E := hE.1
  let : T2Space (GeneralLinear n E) := generalLinear_t2Space_of_finite F E n
  let : LocallyCompactSpace (GeneralLinear n E) := generalLinear_locallyCompactSpace_of_finite F E n
  let : TotallyDisconnectedSpace (GeneralLinear n E) :=
    generalLinear_totallyDisconnectedSpace_of_finite F E n
  let := cyclicGLSemidirect_isTopologicalGroup σ hE.pow_eq_one n
  let Mat := Matrix (Fin n) (Fin n) E
  let G := GeneralLinear n E
  let : NontriviallyNormedField F := LocalGalois.localNormedField F
  let : ProperSpace F := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  let : IsModuleTopology F Mat := inferInstanceAs (IsModuleTopology F (Fin n → Fin n → E))
  let : NormedRing Mat := finiteAlgebraNormedRing F Mat
  let : NormedAlgebra F Mat := finiteAlgebraNormedAlgebra F Mat
  let : CompleteSpace Mat := FiniteDimensional.complete F Mat
  let : ProperSpace Mat := FiniteDimensional.proper F Mat
  let : IsUltrametricDist F := LocalGalois.localNormedField_ultrametric F
  let : IsUltrametricDist Mat := finiteAlgebraNormedRing_ultrametric F Mat
  let : SecondCountableTopology E := (finiteAlgebraTopology F E).2.2
  let : SecondCountableTopology Mat := inferInstanceAs (SecondCountableTopology (Fin n → Fin n → E))
  let : SecondCountableTopology G := generalLinear_secondCountable_of_finiteAlgebra (F := F) (E := E) n
  let : SecondCountableTopology H :=
    (SemidirectProduct.homeomorphProd (cyclicGLAction σ hE.pow_eq_one n)).secondCountableTopology
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  let : MeasurableSpace H := borel H
  let : BorelSpace H := ⟨rfl⟩
  intro W _ _ π hπ hirr s hs
  let α := cyclicAdjointAlgEquiv s
  let S := adjointFixedAlgebra α
  let i : G →* H := SemidirectProduct.inl
  let hi : IsOpenEmbedding i := SemidirectProduct.isOpenEmbedding_inl _
  let j := translatedCosetEmbedding i s
  have hj : IsOpenEmbedding j := isOpenEmbedding_translatedCoset i hi s
  have hjc : IsClosed (range j) := by
    let e := Homeomorph.mulRight s
    change IsClosed (range (e ∘ i))
    rw [range_comp]
    exact e.isClosedMap _ (i.range.isClosed_of_isOpen hi.isOpen_range)
  let ν : Measure H := Measure.haar
  let : (ν.comap j).IsHaarMeasure := isHaarMeasure_comap_translatedCoset i hi s ν
  let : MeasurableSpace S := borel S
  let : BorelSpace S := ⟨rfl⟩
  obtain ⟨ρ, P, T, T₀, C, hC, hzero, hCU, hP, hT, hInv, hSupp, hAgree⟩ :=
    cyclicGLSemisimpleDescent F E σ l n hE π hπ s hs ν
  obtain ⟨V, hV, hVzero, hDensityT₀⟩ :=
    hDensity F E σ l n hE π hπ hirr s hs ν ρ P T T₀ C hC hzero hCU hP hT hInv hSupp hAgree
  let : ρ.measure.IsAddHaarMeasure := ρ.isAddHaar
  obtain ⟨A, hA, hsA, η, hη, hident⟩ := semisimpleDensityRecovery α hj ν ρ.measure
    (isOpenEmbedding_generalLinearVal F E n) (Character.distribution ν π hπ)
    hjc P T T₀ C V hP hT hC.2 hzero hCU hAgree hV hVzero hDensityT₀
  refine ⟨A, hA, by simpa [j, translatedCosetEmbedding] using hsA, η, ?_⟩
  refine isCharacterDensityOn_of_oneHaar ν ((hη.integrableOn (s := A)).locallyIntegrableOn) ?_
  intro f hf
  simpa only [mul_comm] using hident f hf

end Langlands.BaseChange

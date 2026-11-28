import Langlands.BaseChange.TwistedCharacter.CyclicCompactTraceLocalization
import Langlands.BaseChange.TwistedCharacter.ExponentialTraceFourier
import Langlands.HarmonicAnalysis.UnitConjugation.NilpotentOrbitRescaling

/-! # Fourier coset vanishing for the descended cyclic character -/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory MeasureTheory.Measure HarmonicAnalysis UnitConjugation Character
  Function Filter Set Metric _root_.Topology
open scoped SemidirectProduct _root_.Topology

local notation "L(" A "," h ")" => OpenAddSubgroup.toAddSubgroup
  (IsUltrametricDist.closedBall_openAddSubgroup A h)

section Agreement

variable {F A : Type*} [NontriviallyNormedField F] [ProperSpace F]
  [NormedRing A] [NormedAlgebra F A] [CompleteSpace A] [FiniteDimensional F A] [IsUltrametricDist A]
  (α : A ≃ₐ[F] A)

/-- The additive distribution agrees with the slice distribution in all
sufficiently small exponential congruence charts. -/
def AdjointExponentialTestAgreement (D : Distribution (adjointFixedAlgebra α))
    (T : Distribution (adjointConjugationDomain α)) : Prop :=
  let S := adjointFixedAlgebra α
  letI : IsUltrametricDist S := IsUltrametricDist.subtype (fun x : A => x ∈ S)
  ∃ δ > (0 : ℝ), ∀ (t : ℝ) (ht : 0 < t) (ht₁ : t < 1), t ≤ δ →
    ∀ htU : closedBall (0 : S) t ⊆ adjointConjugationDomain α,
      let M := normUnitCongruence (R := S) ht.le ht₁
      ∀ E : closedBall (0 : S) t ≃ₜ M,
        (∀ x, ((E x).val : S) = NormedSpace.exp (x : S)) →
        ExponentialTraceChartAgreement (IsUltrametricDist.isOpen_closedBall (0 : S) ht.ne') E
          (isOpenEmbedding_adjointNormSlice α ht ht₁ htU) D T

end Agreement

/-- Large Fourier cosets of an additive distribution in the actual cyclic
slice vanish away from the cone of a prescribed nilpotent neighborhood. -/
def CyclicDescendedFourierVanishingStatement.{u, v, w} : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] (E : Type v) [CommRing E] [Algebra F E] [TopologicalSpace E]
    [IsTopologicalRing E] [IsModuleTopology F E] (σ : E ≃ₐ[F] E) (l n : ℕ) (hE : IsCyclicAlgebra σ l),
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
    letI : IsUltrametricDist F := LocalGalois.localNormedField_ultrametric F
    letI : IsModuleTopology F Mat := inferInstanceAs (IsModuleTopology F (Fin n → Fin n → E))
    letI : NormedRing Mat := finiteAlgebraNormedRing F Mat
    letI : NormedAlgebra F Mat := finiteAlgebraNormedAlgebra F Mat
    letI : SecondCountableTopology E := (finiteAlgebraTopology F E).2.2
    letI : SecondCountableTopology Mat := inferInstanceAs (SecondCountableTopology (Fin n → Fin n → E))
    letI : CompleteSpace Mat := FiniteDimensional.complete F Mat
    letI : IsUltrametricDist Mat := finiteAlgebraNormedRing_ultrametric F Mat
    letI : MeasurableSpace G := borel G
    haveI : BorelSpace G := ⟨rfl⟩
    letI : MeasurableSpace H := borel H
    haveI : BorelSpace H := ⟨rfl⟩
    ExponentialProductStraighteningStatement F Mat →
    ∀ {W : Type w} [AddCommGroup W] [Module ℂ W] (π : Representation ℂ H W) (hπ : IsAdmissible π),
      π.IsIrreducible → ∀ (s : H), IsCyclicGLSemisimple s → ∀ (ν : Measure H) [ν.IsHaarMeasure],
        let α := cyclicAdjointAlgEquiv s
        let S := adjointFixedAlgebra α
        let U := adjointConjugationDomain α
        let i : G →* H := SemidirectProduct.inl
        let hi : IsOpenEmbedding i := SemidirectProduct.isOpenEmbedding_inl _
        let j := translatedCosetEmbedding i s
        let μ := ν.comap j
        let D := translatedCosetDistribution i hi s (Character.distribution ν π hπ)
        letI : MeasurableSpace S := borel S
        letI : BorelSpace S := ⟨rfl⟩
        letI : IsModuleTopology F S := isModuleTopologyOfFiniteDimensional
        letI : ProperSpace S := FiniteDimensional.proper F S
        letI : IsUltrametricDist S := IsUltrametricDist.subtype (fun x : Mat => x ∈ S)
        ExponentialProductStraighteningStatement F S →
        ∀ (ρ : AdditiveHaarMeasure S) (P : SchwartzBruhat (G × U) →ₗ[ℂ] SchwartzBruhat G) (T : Distribution U),
          SchwartzBruhat.IsTestPushforward (μ.prod (ρ.measure.comap Subtype.val)) μ
            (adjointConjugationOnUnits α) P →
          (letI : IsFiniteMeasureOnCompacts μ := IsFiniteMeasureOnCompacts.comap' ν
              (isOpenEmbedding_translatedCoset i hi s).continuous (isOpenEmbedding_translatedCoset i hi s).measurableEmbedding
           D.comp P = Distribution.tensor (Distribution.ofMeasure μ) T) →
          ∀ Dexp : Distribution S, IsConjugationInvariant Dexp → AdjointExponentialTestAgreement α Dexp T →
          ∀ (ψ : UnitaryAdditiveCharacter F) (d : F), 1 < ‖d‖ → ∀ (V : Set S),
            IsOpen V → nilpotentAnnulus d S ⊆ V →
            let e := pairingCharacter ψ (adjointFixedTracePairing α)
            ∀ he : IsSelfDualBicharacter e,
              ∃ ε > (0 : ℝ), ∀ (t : ℝ) (ht : 0 < t), t < 1 → t ≤ ε → closedBall (0 : S) t ⊆ U →
                let Lₜ := L(S, ht)
                let Adual := he.annihilator (Lₜ : Set S)
                let hLo : IsOpen (Lₜ : Set S) := IsUltrametricDist.isOpen_closedBall _ ht.ne'
                let hLc : IsCompact (Lₜ : Set S) := isCompact_closedBall _ _
                letI : SecondCountableTopology S :=
                  (show IsEmbedding (Subtype.val : S → Mat) from IsEmbedding.subtypeVal).secondCountableTopology
                letI : CompactOpenExhaustion S := compactOpenExhaustion_of_finiteDimensional F S
                ∃ b > (0 : ℝ), ∀ Z : S, b < ‖Z‖ → (¬ ∃ a : F, a ≠ 0 ∧ a • Z ∈ V) →
                  Dexp (bicharacterFourierSB ρ.measure he (latticeCosetTest Adual
                    (he.isOpen_annihilator hLc) (he.isCompact_annihilator_compactOpen Lₜ hLo hLc) Z)) = 0

set_option maxHeartbeats 3000000 in
theorem cyclicDescendedFourierVanishing.{u, v, w} : CyclicDescendedFourierVanishingStatement.{u, v, w} := by
  intro F _ _ _ _ _ E _ _ _ _ _ σ l n hE Mat G H
  let : NeZero l := ⟨hE.pos.ne'⟩
  let : Module.Finite F E := hE.1
  let : IsReduced E := hE.2.2.1
  let : IsArtinianRing E := IsArtinianRing.of_finite F E
  let : IsSemisimpleRing E := IsArtinianRing.isSemisimpleRing_of_isReduced E
  let : T2Space (GeneralLinear n E) := generalLinear_t2Space_of_finite F E n
  let : LocallyCompactSpace (GeneralLinear n E) := generalLinear_locallyCompactSpace_of_finite F E n
  let : TotallyDisconnectedSpace (GeneralLinear n E) := generalLinear_totallyDisconnectedSpace_of_finite F E n
  let := cyclicGLSemidirect_isTopologicalGroup σ hE.pow_eq_one n
  let : NontriviallyNormedField F := LocalGalois.localNormedField F
  let : ProperSpace F := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  let : IsUltrametricDist F := LocalGalois.localNormedField_ultrametric F
  let : IsModuleTopology F Mat := inferInstanceAs (IsModuleTopology F (Fin n → Fin n → E))
  let : NormedRing Mat := finiteAlgebraNormedRing F Mat
  let : NormedAlgebra F Mat := finiteAlgebraNormedAlgebra F Mat
  let : CompleteSpace Mat := FiniteDimensional.complete F Mat
  let : IsUltrametricDist Mat := finiteAlgebraNormedRing_ultrametric F Mat
  let : ProperSpace Mat := FiniteDimensional.proper F Mat
  let : SecondCountableTopology F := LocalFieldTopology.secondCountableTopology F
  let : SecondCountableTopology E := (finiteAlgebraTopology F E).2.2
  let : SecondCountableTopology Mat := inferInstanceAs (SecondCountableTopology (Fin n → Fin n → E))
  let : SecondCountableTopology G := generalLinear_secondCountable_of_finiteAlgebra (F := F) (E := E) n
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  let : MeasurableSpace H := borel H
  let : BorelSpace H := ⟨rfl⟩
  let : MeasurableSpace Mat := borel Mat
  let : BorelSpace Mat := ⟨rfl⟩
  let : CompactOpenExhaustion Mat := compactOpenExhaustion_of_finiteDimensional F Mat
  intro hStraighten W _ _ π hπ hirr s hs ν hν α S U i hi j μ D
  let : MeasurableSpace S := borel S
  let : BorelSpace S := ⟨rfl⟩
  let : MeasurableSpace Sˣ := borel Sˣ
  let : BorelSpace Sˣ := ⟨rfl⟩
  let : ProperSpace S := FiniteDimensional.proper F S
  let : IsUltrametricDist S := IsUltrametricDist.subtype (fun x : Mat => x ∈ S)
  let : IsModuleTopology F S := isModuleTopologyOfFiniteDimensional
  let : CompactOpenExhaustion S := compactOpenExhaustion_of_finiteDimensional F S
  let : SecondCountableTopology S := IsEmbedding.subtypeVal.secondCountableTopology
  let : (ν.comap i).IsHaarMeasure := IsHaarMeasure.comap (mH := inferInstance) ν hi
  let : ν.IsMulRightInvariant := finiteSemidirectHaar (cyclicGLAction σ hE.pow_eq_one n) ν
    (generalLinear_haar_rightInvariant E n (ν.comap i))
  intro hStraightenS ρ P T hP hT Dexp hInv hAgree ψ d hd V hV hNV e he
  have hPair (k : Sˣ) (x z : S) : e (conjugationHomeomorph k x) (conjugationHomeomorph k z) = e x z :=
    congrArg (fun a : F => ψ.complex a) (adjointFixedTracePairing_conjugation α k x z)
  obtain ⟨U₀, hU₀, hNU₀, hTransfer⟩ := nilpotentOrbitRescaling d V hV hNV
  have hNil (x : S) (h₁ : 1 / ‖d‖ ≤ ‖x‖) (h₂ : ‖x‖ ≤ 1) (hx : IsNilpotent x) : x ∈ U₀ :=
    hNU₀ ⟨h₁, h₂, hx⟩
  obtain ⟨εLoc, hεLoc, bLoc, hbLoc, hLoc⟩ :=
    cyclicCompactTraceLocalization F E σ l n hE hStraighten π hπ hirr s hs ν ρ P T hP hT ψ d hd U₀ hU₀ hNil
  obtain ⟨εExp, hεExp, hExp⟩ := exponentialCongruenceHaar (F := F) (A := S)
  obtain ⟨c, hc, εOrb, hεOrb, hSmall, hOrbit⟩ := normUnitOrbitCharacter he hStraightenS hPair
  obtain ⟨εAgree, hεAgree, hCharts⟩ := hAgree
  refine ⟨min εAgree (min εExp (min εLoc εOrb)), lt_min hεAgree (lt_min hεExp (lt_min hεLoc hεOrb)), ?_⟩
  intro t ht ht₁ htε htU
  have htAgree : t ≤ εAgree := htε.trans (min_le_left _ _)
  have htExp : t ≤ εExp := (htε.trans (min_le_right _ _)).trans (min_le_left _ _)
  have htLoc : t ≤ εLoc := ((htε.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _)
  have htOrb : t ≤ εOrb := ((htε.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)
  obtain ⟨expChart, hExpChart, _⟩ := hExp t ht ht₁ htExp
  let Lₜ := L(S, ht)
  let Adual := he.annihilator (Lₜ : Set S)
  let M := normUnitCongruence (R := S) ht.le ht₁
  let hb := isOpenEmbedding_adjointNormSlice α ht ht₁ htU
  let : CompactSpace M := isCompact_iff_compactSpace.mp (isCompact_normUnitCongruence ht.le ht₁)
  have hLo : IsOpen (Lₜ : Set S) := IsUltrametricDist.isOpen_closedBall _ ht.ne'
  have hLc : IsCompact (Lₜ : Set S) := isCompact_closedBall _ _
  have hAc : IsCompact (Adual : Set S) := he.isCompact_annihilator_compactOpen Lₜ hLo hLc
  have hSmallT : max 1 ‖(1 : S)‖ * (c * t) < 1 := by
    exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htOrb (zero_le_one.trans hc))
      (zero_le_one.trans (le_max_left _ _))).trans_lt hSmall
  have hct₀ : 0 ≤ c * t := mul_nonneg (zero_le_one.trans hc) ht.le
  have hct₁ : c * t < 1 := (le_mul_of_one_le_left hct₀ (le_max_left _ _)).trans_lt hSmallT
  let B := normUnitCongruence (R := S) hct₀ hct₁
  have hNorm (k : Sˣ) (hk : k ∈ B) (x : S) : ‖conjugationHomeomorph k x‖ = ‖x‖ :=
    norm_conjugation_eq_of_mem_normUnitCongruence hct₀ hct₁ hSmallT hk x
  have hPres (k : Sˣ) (hk : k ∈ B) (x : S) (hx : x ∈ Lₜ) : conjugationHomeomorph k x ∈ Lₜ := by
    change dist (conjugationHomeomorph k x) 0 ≤ t
    rw [dist_zero_right, hNorm k hk]
    exact dist_zero_right x ▸ hx
  obtain ⟨b, hb₀, hbSpec⟩ := hTransfer B Adual bLoc hAc hbLoc hNorm
  refine ⟨b, hb₀, fun Z hZ hCone => ?_⟩
  obtain ⟨O, hO, hOne, X, hAdd, hModule, hFin, τ, hτ, hTrace⟩ := hOrbit t ht ht₁ hct₁ htOrb Z
  let : AddCommGroup X := hAdd
  let : Module ℂ X := hModule
  let : FiniteDimensional ℂ X := hFin
  let τS : SmoothRep.{0, v, v} ℂ M := SmoothRep.of τ hτ
  let : FiniteDimensional ℂ τS := hFin
  have hEval := exponentialTraceFourier he ρ.measure ht ht₁ expChart hb Dexp T B Z O τ hτ hExpChart
    (hCharts t ht ht₁ htAgree htU expChart hExpChart) hInv hPres (fun k _ => hPair k) hO hOne hTrace
  apply hEval.mp
  by_contra hNonzero
  obtain ⟨Y, hY, hRescale⟩ := hLoc t ht ht₁ htLoc htU he Z B O τS hO hTrace hNonzero
  obtain ⟨hYL, hBack⟩ := hbSpec Z Y hZ hY
  obtain ⟨a, ha, _, haNorm, haU₀⟩ := hRescale hYL
  exact hCone (hBack ⟨a, ha, haNorm, haU₀⟩)

end Langlands.BaseChange

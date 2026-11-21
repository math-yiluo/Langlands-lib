import Langlands.HarmonicAnalysis.HarishChandraSchwartz.CentralProjectionFamily
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.CentralQuotientGeneration
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.DiscreteSeriesSmallRealization
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCuspidalCentralKernelStep
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCuspidalDiscreteUpper
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalXiSquareIntegrable

/-! # Discrete-series actions separate the actual cuspidal Schwartz space -/

noncomputable section

universe u uV

open AlgebraicGeometry CategoryTheory MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme
open Langlands.Plancherel Langlands.QuotientIntegration

namespace Langlands.HarishChandraSchwartz

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

/-- The final vanishing step of VIII.5 with the discrete-series actions
tested in the independent carrier universe `uV`. -/
def RationalCuspidalDiscreteActionSeparationAtUniverseStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (hG : IsConnectedReductive G)
    (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice S) (hν : IsGenericCocharacter i ν)
    (K : OpenSubgroup (rationalPoints G)) (hKc : IsCompact (K : Set (rationalPoints G)))
    (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup)
    (N : ℕ) [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N)),
    IsClosedSubgroup ρ →
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of F))) (s : T.toGrp ⟶ G)
      (hs : IsSplitComponent s),
      let A := (rationalPoints.map s).range
      let hA := hs.isCentralSplitTorus.isCentral.range_le_center
      letI : A.Normal := A.normal_of_le_center hA
      letI : MeasurableSpace (rationalPoints G ⧸ A) := borel _
      letI : Nonempty (CompactOpenSubgroup (rationalPoints G)) := ⟨⟨K, hKc⟩⟩
      ∀ (muA : Measure A) [muA.IsHaarMeasure]
        (muG : Measure (rationalPoints G)) [muG.IsHaarMeasure]
        (mu : Measure (rationalPoints G ⧸ A)) [mu.IsHaarMeasure],
        CentralWeights muA (rationalXi hKc hPK) (rationalHeight (F := F) ρ) →
        ∀ (hL : L2Weights muG (rationalXi hKc hPK) (rationalHeight (F := F) ρ)),
          (∀ χ : unitaryCharacters A, ∀ H : OpenSubgroup (rationalPoints G),
            IsCompact (H : Set (rationalPoints G)) →
            FiniteDimensional ℂ (rationalCuspidalCentralLevelSpan hKc hPK ρ muA
              (χ : A →ₜ* ℂˣ).toMonoidHom H.toSubgroup)) →
          ∀ φ : RationalSchwartzSpace hKc hPK ρ,
            φ ∈ rationalCuspidalSubmodule hKc hPK ρ →
            (∀ ω : DiscreteSeriesClass.{u, uV} A hA mu,
              ∃ hT : HasTemperedCoefficients (rationalXi hKc hPK)
                (rationalHeight (F := F) ρ) ω.val.out.obj.representation,
                schwartzAction hL ω.val.out.property.2 hT
                  (Space.check (rationalXi_inv hG hi hν K.isOpen hKc hPK)
                    (rationalHeight_inv ρ) φ) = 0) →
            φ = 0

/-- Compare the coefficient sum with the same sum in the prescribed carrier
universe and apply Fourier uniqueness on the split center. -/
theorem rationalCuspidalDiscreteActionSeparationAtUniverse :
    RationalCuspidalDiscreteActionSeparationAtUniverseStatement.{u, uV} := by
  intro F _ _ _ _ G _ _ hG S i hi ν hν K hKc hPK N _ ρ hρ T s hs A hA
  let : A.Normal := A.normal_of_le_center hA
  let : MeasurableSpace (rationalPoints G ⧸ A) := borel _
  let : Nonempty (CompactOpenSubgroup (rationalPoints G)) := ⟨⟨K, hKc⟩⟩
  intro muA _ muG _ mu _ hcentral hL hfinite φ hφ haction
  let : T2Space (rationalPoints G) := rationalPoint_t2Space F G
  let : SecondCountableTopology (rationalPoints G) :=
    rationalPoint_secondCountableTopology F G
  let : NonarchimedeanGroup (rationalPoints G) := rationalPoints_nonarchimedeanGroup G
  have hclosed : IsClosed (A : Set (rationalPoints G)) := isClosed_range_splitComponent G s hs
  let : LocallyCompactSpace A := hclosed.locallyCompactSpace
  let : SecondCountableTopology A :=
    inferInstanceAs (SecondCountableTopology (A : Set (rationalPoints G)))
  let : BorelSpace A := Subtype.borelSpace _
  let : MeasurableSpace (LeftQuotient A) := borel _
  let : BorelSpace (LeftQuotient A) := ⟨rfl⟩
  let : BorelSpace (rationalPoints G ⧸ A) := ⟨rfl⟩
  let : muA.IsMulRightInvariant := isMulRightInvariant_of_le_center hA muA
  let : muG.IsMulRightInvariant := rationalHaar_isMulRightInvariant hG muG
  let : muG.IsInvInvariant := Langlands.isInvInvariant_of_isMulRightInvariant muG
  let : mu.IsInvInvariant := (rationalSplitCentralQuotientHaar_invariant hG s hs mu).2
  obtain ⟨muQ, hQ⟩ := compatibleMeasureExists A hclosed muG muA
  apply Space.centralProjectionFamily_injective hcentral hclosed hA
    (hasFGCompactOpenQuotients_splitComponent G hG s hs)
  rw [map_zero]
  funext χ
  let chiHom := (χ : A →ₜ* ℂˣ).toMonoidHom
  have hchi : IsUnitaryCharacter chiHom := isUnitaryCharacter_of_mem_unitaryCharacters χ
  have hupper := rationalCuspidalDiscreteUpperEstimate.{u, uV} F G hG S i hi ν hν K hKc hPK
    N ρ hρ T s hs muA muG hcentral hL mu chiHom (χ : A →ₜ* ℂˣ).continuous hchi (hfinite χ)
  have hmemLift : centralProjection muA chiHom (φ : rationalPoints G → ℂ) ∈
      discreteSeriesCentralCoefficientSpace.{u, max u uV} A hA mu chiHom :=
    hupper ⟨φ, hφ, rfl⟩
  have hmem : centralProjection muA chiHom (φ : rationalPoints G → ℂ) ∈
      discreteSeriesCentralCoefficientSpace.{u, uV} A hA mu chiHom := by
    rw [discreteSeriesCentralCoefficientSpace_eq_of_separable.{u, uV, max u uV} A hA mu chiHom]
    exact hmemLift
  have hle : discreteSeriesCentralCoefficientSpace.{u, uV} A hA mu chiHom ≤
      pairingAnnihilator muG (φ : rationalPoints G → ℂ) := by
    apply (discreteSeriesCentralCoefficientSpace_le_iff A hA mu chiHom _).mpr
    intro ω _
    obtain ⟨hT, hzero⟩ := haction ω
    have hsq : IsSquareIntegrableModCentralSubgroup A hA ω.val.out.obj.representation mu := by
      change IsDiscreteSeriesClass A hA mu (Quotient.mk _ ω.val.out)
      rw [Quotient.out_eq ω.val]
      exact ω.property
    obtain ⟨b⟩ := isUnitarizable_of_isSquareIntegrableModCentralSubgroup A hA mu
      CompactOpenSubgroup.cofinal hsq
    apply iSup_le
    intro ℓ
    rintro _ ⟨v, rfl⟩
    exact coefficient_mem_pairingAnnihilator hL ω.val.out.property.2 hT
      (rationalXi_inv hG hi hν K.isOpen hKc hPK) (rationalHeight_inv ρ) b hzero v ℓ
  have hcont : Continuous (centralProjection muA chiHom (φ : rationalPoints G → ℂ)) := by
    obtain ⟨H, hH⟩ := (mem_schwartzSubmodule_iff _ _).mp (Space.coe_mem φ)
    exact (IsBiInvariant.isLocallyConstant (hH.1.centralProjection (μA := muA) hA chiHom)).continuous
  exact centralProjection_eq_zero_of_mem_pairingAnnihilator hclosed hQ hchi hcont (hle hmem)

/-- The VIII.5 implication at the carrier universe of the upper inclusion. -/
def RationalCuspidalDiscreteActionSeparationStatement : Prop :=
  RationalCuspidalDiscreteActionSeparationAtUniverseStatement.{u, max u uV}

/-- Apply the vanishing implication at the carrier universe of the upper inclusion. -/
theorem rationalCuspidalDiscreteActionSeparation :
    RationalCuspidalDiscreteActionSeparationStatement.{u, uV} :=
  rationalCuspidalDiscreteActionSeparationAtUniverse.{u, max u uV}

end Langlands.HarishChandraSchwartz

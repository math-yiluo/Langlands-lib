import Langlands.BaseChange.TwistedCharacter.AdjointExponentialCutoff
import Langlands.BaseChange.TwistedCharacter.DescendedLocalDensityReduction
import Langlands.BaseChange.TwistedCharacter.ExponentialDensityTransfer
import Langlands.HarmonicAnalysis.UnitConjugation.CharacteristicHoweRestriction
import Langlands.HarmonicAnalysis.UnitConjugation.FourierConjugation
import Langlands.HarmonicAnalysis.UnitConjugation.FourierLocalDensity

/-! # From Fourier coset vanishing to twisted character integrability -/

noncomputable section

namespace Langlands.HarmonicAnalysis.UnitConjugation

open Set

/-- The small exponential product assertion for complete ultrametric normed algebras. -/
def UltrametricExponentialProductStraighteningStatement.{u, v} : Prop :=
  ∀ (F : Type u) [NontriviallyNormedField F] [CharZero F] [IsUltrametricDist F]
    (A : Type v) [NormedRing A] [NormedAlgebra F A] [IsUltrametricDist A] [CompleteSpace A],
    ExponentialProductStraighteningStatement F A

/-- Compact conjugacy containment and conic Howe finiteness in the characteristic size. -/
def LocalAlgebraCharacteristicHoweDataStatement.{u, v} : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F],
    letI : NontriviallyNormedField F := LocalGalois.localNormedField F
    ∀ (A : Type v) [NormedRing A] [NormedAlgebra F A] [FiniteDimensional F A]
      [IsSemisimpleRing A] [IsUltrametricDist A],
      (∃ ω : Set A, IsCompact ω ∧ {x | characteristicSize F x ≤ 1} ⊆ conjugationSaturation ω) ∧
        CharacteristicConicFiniteness (A := A) F

end Langlands.HarmonicAnalysis.UnitConjugation

namespace Langlands.BaseChange

open MeasureTheory MeasureTheory.Measure HarmonicAnalysis UnitConjugation Character
  Function Set Metric _root_.Topology
open scoped SemidirectProduct _root_.Topology

/-- The actual descended distributions have local densities given exponential product
straightening, characteristic conic restriction data and Fourier regularity. -/
def CyclicDescendedDensityFromFourierStatement.{u, v, w} : Prop :=
  UltrametricExponentialProductStraighteningStatement.{u, v} →
  LocalAlgebraCharacteristicHoweDataStatement.{u, v} →
  LieAlgebraFourierRegularityStatement.{u, v} →
  CyclicGLDescendedLocalDensityStatement.{u, v, w}

set_option maxHeartbeats 5200000 in
set_option synthInstance.maxHeartbeats 220000 in
theorem cyclicDescendedDensityFromFourier.{u, v, w} : CyclicDescendedDensityFromFourierStatement.{u, v, w} := by
  intro hStraighten hHowe hHC F _ _ _ _ _ E _ _ _ _ _ σ l n hE Mat G H
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
  let : SecondCountableTopology E := (finiteAlgebraTopology F E).2.2
  let : SecondCountableTopology Mat := inferInstanceAs (SecondCountableTopology (Fin n → Fin n → E))
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  let : MeasurableSpace H := borel H
  let : BorelSpace H := ⟨rfl⟩
  intro W _ _ π hπ hirr s hs ν hν α S U i hi μ D
  let : MeasurableSpace S := borel S
  let : BorelSpace S := ⟨rfl⟩
  let : MeasurableSpace Sˣ := borel Sˣ
  let : BorelSpace Sˣ := ⟨rfl⟩
  let : ProperSpace S := FiniteDimensional.proper F S
  let : IsUltrametricDist S := IsUltrametricDist.subtype (fun x : Mat => x ∈ S)
  let : IsModuleTopology F S := isModuleTopologyOfFiniteDimensional
  let : CompactOpenExhaustion S := compactOpenExhaustion_of_finiteDimensional F S
  let : SecondCountableTopology S := IsEmbedding.subtypeVal.secondCountableTopology
  have hα : Module.End.IsSemisimple α.toLinearMap := hs
  let : IsSemisimpleRing S := isSemisimpleRing_adjointFixedAlgebra α hα
  intro ρ P T T₀ C hC h₀ hCU hP hT hInv _ hAgree
  let : ρ.measure.IsAddHaarMeasure := ρ.isAddHaar
  obtain ⟨Dexp, hDInv, hChart, r₀, hr₀, hChart₀⟩ :=
    adjointExponentialCutoff α C T₀ T hC h₀ hCU hInv hAgree (invariantExponentialDomain F S)
  obtain ⟨ψ⟩ := nonempty_unitaryAdditiveCharacter F
  obtain ⟨d, hd⟩ := NormedField.exists_one_lt_norm F
  let B := adjointFixedTracePairing α
  have hB : IsInvariantPairing B :=
    ⟨adjointFixedTracePairing_isSymm α, adjointFixedTracePairing_nondegenerate α hα,
      adjointFixedTracePairing_conjugation α⟩
  let he := isSelfDualBicharacter_pairingCharacter ψ hB.isSymm hB.nondegenerate
  obtain ⟨hUnit, hFin⟩ := hHowe F S
  obtain ⟨δ, hδ, hCut⟩ := characteristicHoweRestriction (A := S) d hUnit hFin hd
  let V := characteristicCone (A := S) F δ
  obtain ⟨ε, hε, hVan⟩ := cyclicDescendedFourierVanishing F E σ l n hE
    (hStraighten F Mat) π hπ hirr s hs ν (hStraighten F S) ρ P T hP hT Dexp hDInv hChart ψ d hd V
    (isOpen_characteristicCone δ) (nilpotentAnnulus_subset_characteristicCone hd hδ) he
  have hUo : IsOpen U := isOpen_adjointConjugationDomain α
  have hU₀ : (0 : S) ∈ U := hCU h₀
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp (hUo.mem_nhds hU₀)
  let t := min (r / 2) (min (1 / 2 : ℝ) ε)
  have ht : 0 < t := lt_min (half_pos hr) (lt_min (by norm_num) hε)
  have ht₁ : t < 1 := ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (by norm_num)
  have htU : closedBall (0 : S) t ⊆ U :=
    (closedBall_subset_ball ((min_le_left _ _).trans_lt (half_lt_self hr))).trans hrU
  let L := (IsUltrametricDist.closedBall_openAddSubgroup S ht).toAddSubgroup
  let L' := he.annihilator (L : Set S)
  have hLo : IsOpen (L : Set S) := IsUltrametricDist.isOpen_closedBall _ ht.ne'
  have hLc : IsCompact (L : Set S) := isCompact_closedBall _ _
  have hL'o : IsOpen (L' : Set S) := he.isOpen_annihilator hLc
  have hL'c : IsCompact (L' : Set S) := he.isCompact_annihilator_compactOpen L hLo hLc
  let Df := (bicharacterFourierSB ρ.measure he).dualMap Dexp
  have hPair (k : Sˣ) (x y : S) : pairingCharacter ψ B (conjugationHomeomorph k x)
      (conjugationHomeomorph k y) = pairingCharacter ψ B x y :=
    congrArg (fun z : F => ψ.complex z) (hB.conj_invariant k x y)
  have hDf : IsConjugationInvariant Df :=
    fourierConjugation ρ.measure he Dexp (pairingHaarPreservation B ρ.measure hB) hPair hDInv
  have hLf : ∃ b > 0, ∀ x : S, b < ‖x‖ → x ∉ V → Df (latticeCosetTest L' hL'o hL'c x) = 0 := by
    obtain ⟨b, hb, hBnd⟩ := hVan t ht ht₁ ((min_le_right _ _).trans (min_le_right _ _)) htU
    refine ⟨b, hb, fun x hx hxV => hBnd x hx ?_⟩
    rintro ⟨a, ha, hax⟩
    exact hxV ((smul_mem_characteristicCone_iff δ ha x).mp hax)
  obtain ⟨M, hMo, hMc, _, ω, Dsmall, hω, hDsmall, hEq⟩ := hCut L' hL'o hL'c Df hDf hLf
  let J := he.annihilator (M : Set S)
  have hJo : IsOpen (J : Set S) := he.isOpen_annihilator hMc
  have hJM : he.annihilator (J : Set S) = M := compactOpenDoubleAnnihilator he M ρ.measure hMo hMc
  obtain ⟨θ, hθ, hDens⟩ := exists_density_on_subgroup_of_fourierAgreement hHC ψ hB ρ J hω Dexp Dsmall hDsmall (by
    intro g hg
    have hgM : g ∈ latticeInvariantTests M := by
      change ∀ a ∈ M, ∀ x, g (x + a) = g x
      simpa only [hJM] using hg
    change Df g = Dsmall g
    exact congrArg (fun f : Module.Dual ℂ (latticeInvariantTests M) => f ⟨g, hgM⟩) hEq.symm)
  obtain ⟨r₁, hr₁, hrB⟩ := Metric.mem_nhds_iff.mp ((hJo.inter hUo).mem_nhds ⟨J.zero_mem, hU₀⟩)
  obtain ⟨rE, hrE, hEcong⟩ := exponentialCongruenceHaar (F := F) (A := S)
  let q := min (r₁ / 2) (min (1 / 2 : ℝ) (min r₀ rE))
  have hq : 0 < q := lt_min (half_pos hr₁) (lt_min (by norm_num) (lt_min hr₀ hrE))
  have hq₁ : q < 1 := ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (by norm_num)
  have hqB : closedBall (0 : S) q ⊆ (J : Set S) ∩ U :=
    (closedBall_subset_ball ((min_le_left _ _).trans_lt (half_lt_self hr₁))).trans hrB
  have hqU : closedBall (0 : S) q ⊆ U := hqB.trans inter_subset_right
  have hqJ : closedBall (0 : S) q ⊆ (J : Set S) := hqB.trans inter_subset_left
  have hqr : q ≤ min r₀ rE := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨Ξ, hΞ, hHaar⟩ := hEcong q hq hq₁ (hqr.trans (min_le_right _ _))
  let K := normUnitCongruence (R := S) hq.le hq₁
  let : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_normUnitCongruence hq.le hq₁)
  let b := adjointNormSlice α hq hq₁ hqU
  let j : K → S := (Subtype.val : U → S) ∘ b
  have hj : IsOpenEmbedding j := hUo.isOpenEmbedding_subtypeVal.comp (isOpenEmbedding_adjointNormSlice α hq hq₁ hqU)
  have hMeasure : MeasurePreserving Ξ (ρ.measure.comap (Subtype.val : closedBall (0 : S) q → S))
      (ρ.measure.comap j) := (hHaar ρ.measure).2
  have hBo : IsOpen (closedBall (0 : S) q) := IsUltrametricDist.isOpen_closedBall _ hq.ne'
  have hCompare := hChart₀ q hq hq₁ (hqr.trans (min_le_left _ _)) hqU Ξ hΞ
  obtain ⟨η, hη, hηEq⟩ := exponentialDensityTransfer hBo Ξ hj ρ.measure Dexp T₀ hMeasure hCompare
    ⟨θ, hθ, fun f hf => hDens f (hf.trans hqJ)⟩
  have hj₀ : (0 : S) ∈ range j := by
    refine ⟨(1 : K), ?_⟩
    change (1 : S) - 1 = 0
    exact sub_self _
  exact ⟨range j, hj.isOpen_range, hj₀, η, hη.locallyIntegrable.locallyIntegrableOn _, hηEq⟩

/-- The local Fourier hypotheses imply twisted character integrability in the full
cyclic setting. -/
def TwistedCharacterFromFourierStatement.{u, v, w} : Prop :=
  UltrametricExponentialProductStraighteningStatement.{u, v} →
  LocalAlgebraCharacteristicHoweDataStatement.{u, v} →
  LieAlgebraFourierRegularityStatement.{u, v} →
  TwistedCharacterLocalIntegrabilityStatement.{u, v, w}

theorem twistedCharacterFromFourier.{u, v, w} : TwistedCharacterFromFourierStatement.{u, v, w} := by
  intro hExp hHowe hHC
  exact twistedCharacterFromDescendedLocalDensity (cyclicDescendedDensityFromFourier hExp hHowe hHC)

end Langlands.BaseChange

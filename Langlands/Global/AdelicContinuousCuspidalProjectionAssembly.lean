import Langlands.Global.AdelicContinuousCuspidalProjectionStatement
import Langlands.Global.AdelicLeviFibrePairingComparison
import Langlands.Global.AdelicLeviFibreSmoothingCuspidality
import Langlands.Global.AdelicParabolicReproducingKernelProof
import Langlands.Global.AdelicCuspidalTestAlgebra
import Langlands.Global.AdelicNormOneHaarRightInvariantProof

/-! # Assembly of the continuous cuspidal projection -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Set
open scoped CategoryTheory.MonObj CompactlySupported

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  PositiveRealTorus RepresentationGrowth

section Positive

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G) (J : StandardIndex F G fam.i fam.ν)

local notation "A" => AdelicGroupPoints F G
local notation "M" => fam.M J
local notation "AM" => AdelicGroupPoints F M
local notation "dq₁" => normOneRationalQuotientHaarMeasure F M
local notation "jM" => fam.l J ≫ fam.p J
local notation "ι" => map F M G jM
local notation "Γ" => parabolicQuotientSubgroup F (fam.p J) (fam.iU J) (fam.l J)

private theorem exists_continuousCuspidalProjection_pos
    (hAvg : LeviRadicalAverageTestFunctionStatement.{u})
    (hDecay : NormOnePartialConvolutionRapidDecayStatement.{u})
    (K : Subgroup A) (hK : IsMaximalCompactSubgroup F G K)
    (hK₀ : IsIwasawaCompact (fam.p ⟨∅, Set.empty_subset _⟩) K)
    (hKM : ∀ P : StandardIndex F G fam.i fam.ν,
      IsMaximalCompactSubgroup F (fam.M P)
        (K.comap (map F (fam.M P) G (fam.l P ≫ fam.p P)).toMonoidHom))
    {N d : ℕ} (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N)
    (hs : SmoothOfRelativeDimension d G.X.hom) (hrho : IsClosedSubgroup rho)
    (φ : A → ℂ)
    (hφ : fam.IsAutomorphicOn hs (K.comap (ofInfinite F G).toMonoidHom) rho J φ) :
    ∃ ψ : A → ℂ, fam.IsModerateContinuousOnParabolic rho J ψ ∧ fam.IsCuspidalAlong J ψ ∧
      ∀ t : AM → ℂ, fam.IsLeviCuspForm (K.comap (ofInfinite F G).toMonoidHom) rho J t →
        ∀ g, Integrable (fam.leviPairingIntegrand J φ g t) dq₁ ∧
          Integrable (fam.leviPairingIntegrand J ψ g t) dq₁ ∧
          fam.leviPairing J φ g t = fam.leviPairing J ψ g t := by
  classical
  let hM := (fam.isCompatible J).levi.isConnectedReductive
  let : IsAffineHom (fam.M J).X.hom := hM.isAffineHom
  let := normOneHaarRightInvariant F M hM.smooth hM.connectedSpace
  let rhoM := jM ≫ rho
  let : IsClosedImmersion rho.hom.hom.left := hrho
  let : IsClosedImmersion (fam.l J).hom.hom.left := (fam.isCompatible J).levi.isClosedSubgroup
  let : IsClosedImmersion (fam.p J).hom.hom.left := (fam.isCompatible J).parabolic.isClosedSubgroup
  have hrhoM : IsClosedSubgroup rhoM := by
    change IsClosedImmersion ((fam.l J ≫ fam.p J) ≫ rho).hom.hom.left
    simp only [Grp.comp_hom_hom, Over.comp_left]
    infer_instance
  obtain ⟨T, i, hi, _⟩ := adelicPositiveDecompositionStatement F M hM
  let hc := hi.1.2
  have hi₀ := characterRestrict_injective_of_centralSplitTorusCharacter centralSplitTorusCharacter hM hi
  let := characterRestrictionFiniteIndexStatement F M hM T i hi
  obtain ⟨I, _, ⟨e⟩⟩ := hi.1.1.1
  let := Fintype.ofFinite I
  let Pos := intrinsicSubgroup F T
  let dp := normalizedPositiveHaarMeasure F M T i hi₀ I e hc
  have hIw : IsIwasawaCompact (fam.p J) K :=
    fam.isIwasawaCompact_of_le (Set.empty_subset J.val) hK₀
  obtain ⟨α₀, hα, _, hrep⟩ := parabolicReproducingKernel F G fam K hK hK₀ hKM rho hs hrho J φ hφ
  let α : C_c(A, ℂ) := ⟨⟨α₀, hα.1.1⟩, hα.2.1⟩
  have hrep' : AdelicGroupPoints.rightConvolution F G α φ = φ := hrep
  have hφi : IsLeftInvariantUnder F G Γ φ := hφ.1
  have hφc : Continuous φ := hφ.2.1.1
  have hφh := (hasModerateGrowthFunction_iff_hasHeightGrowth hN φ).mp hφ.2.2.2.2
  obtain ⟨L, hL, hφL⟩ := hφ.2.1.2.2
  obtain ⟨n, k₀, a, ha, haL, hdec⟩ :=
    exists_maximalCompact_rightTranslate_decomposition K hK hφc hφ.2.2.1 L hL hφL
  let k (j : Fin n) : A := k₀ j
  let β (j : Fin n) := StandardParabolicFamily.compactRightAverageCc K hIw.isCompact (a j) (ha j) α
  have hβ (j : Fin n) : IsAdelicTestFunction F G (β j) :=
    isAdelicTestFunction_maximalCompactRightAverage hs K hK (a j) (ha j) L hL (haL j) hα
  obtain ⟨c, _, hIwExp⟩ := fam.exists_leviPairing_rightConvolution_eq_fibreExpansion
    J T i hi₀ I e hc rho hN K hIw
  have hExp (s : AM → ℂ) (hsc : Continuous s)
      (hsi : IsLeftInvariantUnder F M (rationalSubgroup F M) s) (hsd : HasRapidDecayOnNormOneRepresentatives rhoM s)
      (g : A) :
      fam.leviPairing J φ g s = (c : ℝ) • ∑ j, ∫ b : Pos,
        fam.leviFibrePairingExpansionIntegrand J T i (β j) (fam.leviFibre J φ (k j))
          (positiveQuotientOfNormOneRestriction T i hi₀ I e hc hsc hsi) g b ∂dp :=
    (congrArg (fun f => fam.leviPairing J f g s) hrep'.symm).trans
      (hIwExp α φ hφc hφi hφh k₀ a ha hdec s hsc hsi hsd g)
  have hβL (j l : Fin n) : IsAdelicTestFunction F M (fam.radicalKernelCc J (β l) (k j) 1) :=
    fam.isAdelicTestFunction_radicalKernel J hAvg (hβ l) (k j) 1
  obtain ⟨_, r, hvec⟩ := fam.finiteLeviFibreVector_properties J T i hi₀ I e hc β k φ c
    hDecay rho hN hrho hβL hφc hφi hφh
  let ψ := fam.finiteLeviFibreProjection J T i hi₀ I e hc β k φ c
  have hψ := fam.isModerateContinuousOnParabolic_finiteLeviFibreProjection
    J T i hi₀ I e hc β k φ c rho hN hrho K hIw ⟨r, hvec⟩
  have hψcusp := fam.isCuspidalAlong_finiteLeviFibreProjection
    J T i hi₀ I e hc β k φ c (fun j => (hvec j).1)
  refine ⟨ψ, hψ, hψcusp, fun t ht g => ?_⟩
  let Kinf := K.comap (ofInfinite F G).toMonoidHom
  have hKi : CompactIwasawa.IsMaximalCompact (fam.leviInfiniteCompact Kinf J) := by
    have h := (hKM J).isMaximalCompact_comap_ofInfinite
    convert h using 1
    ext x
    change ofInfinite F G ((fam.M J).affinePointsTarget jM
        (CommAlgCat.of F (NumberField.InfiniteAdeleRing F)) x) ∈ K ↔
      ι (ofInfinite F M x) ∈ K
    rw [map_ofInfinite]
  have hAuto : IsAutomorphicFunctionOn F M (fam.leviSmooth J)
      (adelicDifferentialCommutator_of_smooth F M (fam.leviSmooth J))
      (rationalSubgroup F M) (fam.leviInfiniteCompact Kinf J) rhoM t := by
    simpa only [rhoM, Category.assoc] using ht.1
  obtain ⟨D, hD, hbound⟩ := exists_rationalRepresentatives_cuspForm_rapidDecay hM (fam.leviSmooth J)
    (fam.leviInfiniteCompact Kinf J) hKi rhoM hN hrhoM t hAuto ht.2
  have htd : HasRapidDecayOnNormOneRepresentatives rhoM t := by
    intro m
    obtain ⟨B, hB⟩ := hbound m
    refine ⟨max B 0, le_max_right _ _, fun x => ?_⟩
    obtain ⟨r₀, hr₀⟩ := hD x
    exact ⟨r₀, (hB _ hr₀).trans (le_max_left _ _)⟩
  have hψh := (hasModerateGrowthFunction_iff_hasHeightGrowth hN ψ).mp hψ.2.2
  have htc : Continuous t := hAuto.2.1.1
  have hti : IsLeftInvariantUnder F M (rationalSubgroup F M) t := hAuto.1
  exact ⟨fam.integrable_leviPairingIntegrand_of_heightGrowth J rho hN hφh hφc hφi htc hti htd g,
    fam.integrable_leviPairingIntegrand_of_heightGrowth J rho hN hψh hψ.2.1 hψ.1 htc hti htd g,
    (fam.leviPairing_finiteLeviFibreProjection_eq_of_fibreExpansion J T i hi₀ I e hc
      hAvg hDecay rho hN hrho K hIw β k φ c hβ hφc hφi hφh hExp t htc hti ht.2 htd g).symm⟩

end Positive

/-- The two analytic kernel theorems give the continuous cuspidal projection by finite
Iwasawa unfolding and the cuspidal Hilbert-space construction. -/
theorem continuousCuspidalProjectionExistence_of_analyticInputs
    (hAvg : LeviRadicalAverageTestFunctionStatement.{u})
    (hDecay : NormOnePartialConvolutionRapidDecayStatement.{u}) :
    ContinuousCuspidalProjectionExistenceStatement.{u} := by
  intro F _ _ G _ _ _ fam K hK hK₀ hKM N d rho hs hrho Kinf J φ hφ
  by_cases hN : 0 < N
  · exact exists_continuousCuspidalProjection_pos fam J hAvg hDecay K hK hK₀ hKM rho hN hs hrho φ hφ
  have h0 : N = 0 := Nat.eq_zero_of_not_pos hN
  subst N
  let : IsClosedImmersion rho.hom.hom.left := hrho
  let : Mono rho.hom.hom := Over.mono_of_mono_left _
  have hpts (X : Over (Spec (CommRingCat.of F))) : Subsingleton (X ⟶ G.X) :=
    ⟨fun x y => rho.pointMatrix_injective X (Subsingleton.elim _ _)⟩
  have hG : Subsingleton (AdelicGroupPoints F G) := hpts _
  have hCusp : fam.IsCuspidalAlong J φ := by
    intro Q hQ
    exfalso
    apply hQ.not_ge
    rw [fam.le_iff_range_le]
    intro X x _
    have hx : x = 1 := (hpts X).elim _ _
    rw [hx]
    exact ((SubgroupFunctor.range (fam.p Q)).carrier X).one_mem
  let M := fam.M J
  let j := fam.l J ≫ fam.p J
  let hj : IsClosedImmersion j.hom.hom.left := (fam.isCompatible J).levi.isClosedSubgroup.comp
    (fam.isCompatible J).parabolic.isClosedSubgroup
  have hM : Subsingleton (AdelicGroupPoints F M) :=
    ⟨fun x y => (isClosedEmbedding_map F M G j).injective (hG.elim _ _)⟩
  let := AdelicSiegelFactors.isFiniteMeasure_normOneRationalQuotientHaarMeasure_of_connectedReductive F M
    (fam.isCompatible J).levi.isConnectedReductive
  refine ⟨φ, ⟨hφ.1, hφ.2.1.1, hφ.2.2.2.2⟩, hCusp, fun t _ g => ?_⟩
  have hint : Integrable (fam.leviPairingIntegrand J φ g t) (normOneRationalQuotientHaarMeasure F M) := by
    refine (integrable_const (φ 1 * starRingEnd ℂ (t 1))).congr (Filter.Eventually.of_forall fun q => ?_)
    unfold StandardParabolicFamily.leviPairingIntegrand
    rw [hG.elim (_ * g) 1, hM.elim (((Quotient.out q : normOneSubgroup F M) : AdelicGroupPoints F M)) 1]
  exact ⟨hint, hint, rfl⟩

end Langlands.Global

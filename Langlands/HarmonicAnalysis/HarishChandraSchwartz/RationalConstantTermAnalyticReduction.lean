import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalXiGlobalUpperBoundStatement
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalUnipotentWeightIntegrabilityStatement
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalLeviXiLowerBoundStatement
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalLeviXiReversal
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalReversedModulus
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSigmaProduct
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalConstantTermCompactCover
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.ConstantTermRepresentativeEstimate

/-! # Actual constant-term decay from the three analytic prerequisites -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal ENNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.SpecialCompact
open Langlands.Aubert.General.RationalPointFamily

namespace Langlands.HarishChandraSchwartz

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

/-- The original standard radical is the opposite radical of the negated
standard cocharacter in the reversed chamber. -/
theorem oppositeUnipotent_neg_standard_eq
    {F : Type u} [Field F]
    {S : CommGroupScheme (Spec (CommRingCat.of F))}
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (hG : IsConnectedReductive G) {i : S.toGrp ⟶ G}
    (hi : IsMaximalSplitTorus i) {ν : cocharacterLattice S}
    (hν : IsGenericCocharacter i ν) {J : Set (characterLattice S)}
    {ζ : cocharacterLattice S} (hζ : IsStandardCocharacter i ν J ζ) :
    oppositeUnipotent i (-ζ) = standardUnipotentPoints i ν J := by
  obtain ⟨-, hc⟩ := standardCocharacter F G hG S i hi ν hν J hζ.subset
  obtain ⟨-, -, hU⟩ := hc ζ hζ
  unfold oppositeUnipotent standardUnipotentPoints
  rw [groupHom_neg_comp_eq_oppositeCocharacter]
  change (Dynamic.unipotent (Dynamic.inverseCocharacter
    (Dynamic.inverseCocharacter (CommGroupScheme.groupHom ζ ≫ i)))).carrier _ = _
  rw [Dynamic.inverseCocharacter_inverseCocharacter, hU]

set_option maxHeartbeats 1600000 in
/-- The exact reduction retains the three named analytic estimates as
premises; none is asserted by this theorem. -/
theorem rationalConstantTermEstimate_of_analyticInputs
    (hGlobal : RationalXiGlobalUpperBoundStatement.{u})
    (hIntegral : RationalUnipotentWeightIntegrabilityStatement.{u})
    (hLower : RationalLeviXiLowerBoundStatement.{u}) :
    RationalConstantTermEstimateStatement.{u} := by
  intro F _ _ _ _ G _ _ hG S i hi ν hν J hJ K0 hK0o hK0c hbasis hcover hLcover
    K hKo hKc hPK hM N _ ρ hρ nuU _
  have hνr := hν.neg i ν
  have hJr : Neg.neg '' J ⊆ simpleRelativeRoots i (-ν) := by
    rintro _ ⟨α, hα, rfl⟩
    exact neg_mem_simpleRelativeRoots i ν (relativeRootNegation F G hG S i hi) (hJ hα)
  have hbasisr := simultaneousStandardBasisAt_reversed hG hi hν hbasis
  have hcoverr := finiteCartanCovering_reversed hG hi hcover
  have hLcoverr := standardLeviCartanCovering_reversed hG hi hν hJ hLcover
  have hPKr := IsIwasawaPair.rationalChangeMinimal hG hi hν hνr hPK
  have hMr := IsIwasawaPair.reversedLevi hG hi hν hJ hM
  have hLevi := standardLeviPoints_reversed hG hi hν hJ
  obtain ⟨F0, hCoverRep⟩ := isDoubleCosetCover_rationalLeviCartanRepresentatives hLcoverr
  let T : Set (standardLeviPoints i ν J) := {m | ∃ f ∈ F0, ∃ a : rationalPoints S.toGrp,
    a ∈ CocharacterUniformizer.CAplus F S (Neg.neg '' J) ∧
      (m : rationalPoints G) = (f : rationalPoints G) * rationalPoints.map i a}
  have hCoverT : IsDoubleCosetCover (K0.subgroupOf (standardLeviPoints i ν J)) T := by
    dsimp only [T]
    rw [← hLevi]
    exact hCoverRep
  let er : standardLeviPoints i ν J ≃ₜ* standardLeviPoints i (-ν) (Neg.neg '' J) :=
    subgroupContinuousMulEquiv (ContinuousMulEquiv.refl (rationalPoints G)) (fun x => by
      change x ∈ standardLeviPoints i ν J ↔ x ∈ standardLeviPoints i (-ν) (Neg.neg '' J)
      rw [hLevi])
  have her : ∀ m : standardLeviPoints i ν J, (er m : rationalPoints G) = m := fun _ => rfl
  let e : standardLeviPoints i ν J → ℝ := fun m =>
    iwasawaWeight hPKr (rationalMinimalModulus i (-ν)) (m : rationalPoints G)
  let eM : standardLeviPoints i ν J → ℝ := fun m =>
    iwasawaWeight hMr (standardLeviMinimalModulusOf i (-ν) (Neg.neg '' J)) (er m)
  let w : standardUnipotentPoints i ν J → ℝ := fun u =>
    iwasawaWeight hPKr (rationalMinimalModulus i (-ν)) (u : rationalPoints G)
  have hPmem : ∀ m ∈ T, (m : rationalPoints G) ∈ standardParabolicPoints i (-ν) ∅ := by
    rintro m ⟨f, hf, a, ha, hm⟩
    rw [hm]
    apply (standardParabolicPoints i (-ν) ∅).mul_mem
    · exact centralizerPoints_le_standardParabolicPoints i (-ν) ∅ f.2
    · have hx := map_mem_standardLeviPoints_empty (i := i) (ν := -ν) (𝟙 S.toGrp) a
      rw [Category.id_comp] at hx
      exact standardLevi_le_standardParabolic i (-ν) ∅ _ hx
  have heM : ∀ m ∈ T,
      e m * NNReal.sqrt (standardUnipotentModulus i ν J m) ≤ eM m := by
    intro m hm
    have hp := hPmem m hm
    let p : (standardParabolicPoints i (-ν) ∅).subgroupOf
        (standardLeviPoints i (-ν) (Neg.neg '' J)) := ⟨er m, hp⟩
    have hfact := rationalMinimalModulus_reversed_mul hG hi hν hJ m p rfl
    change rationalMinimalModulus i (-ν) ⟨m, hp⟩ * standardUnipotentModulus i ν J m =
      standardLeviMinimalModulusOf i (-ν) (Neg.neg '' J) p at hfact
    have he : e m = NNReal.sqrt
        (rationalMinimalModulus i (-ν) ⟨m, hp⟩ : ℝ≥0) := by
      have h := iwasawaWeight_mul (hPK := hPKr)
        (fun q hq => rationalMinimalModulus_eq_one i (-ν) hKo hKc q hq) hp K.one_mem
      simpa only [mul_one] using h
    have heM : eM m = NNReal.sqrt
        (standardLeviMinimalModulusOf i (-ν) (Neg.neg '' J) p : ℝ≥0) := by
      have h := iwasawaWeight_mul (hPK := hMr)
        (fun q hq => standardLeviMinimalModulusOf_eq_one hKo hKc hG hi hνr hJr q hq)
        p.2 (K.subgroupOf (standardLeviPoints i (-ν) (Neg.neg '' J))).one_mem
      simpa only [mul_one] using h
    apply le_of_eq
    rw [he, heM]
    simpa only [Units.val_mul, NNReal.sqrt_mul, NNReal.coe_mul] using
      congrArg (fun c : ℝ≥0ˣ => (NNReal.sqrt (c : ℝ≥0) : ℝ)) hfact
  have h44 : UnipotentXiBound (rationalXi hKc hPK) (rationalHeight (F := F) ρ) T e w := by
    obtain ⟨D, C, hCpos, hC⟩ := hGlobal F G hG S i hi (-ν) hνr
      K0 hK0o hK0c hbasisr hcoverr K hKo hKc hPKr N ρ hρ
    refine ⟨D, C, fun m hm u => ?_⟩
    have h := hC ((m : rationalPoints G) * u)
    rw [rationalXi_changeMinimal hG hi hν hνr hKo hKc hPK hPKr] at h
    rw [iwasawaWeight_mul_of_mem
      (fun p hp => rationalMinimalModulus_eq_one i (-ν) hKo hKc p hp) (hPmem m hm)] at h
    simpa only [Real.rpow_natCast, mul_assoc, e, w] using h
  have h11 : XiLowerBound (rationalLeviXi hKc hM) T eM := by
    obtain ⟨C, hCpos, hC⟩ := hLower F G hG S i hi (-ν) hνr (Neg.neg '' J) hJr
      K0 hK0o hK0c hbasisr K hKo hKc hMr F0
    refine ⟨C, fun m hm => ?_⟩
    have h := hC (er m) hm
    rwa [rationalLeviXi_reversed hG hi hν hJ hKo hKc hM hMr m (er m) rfl] at h
  have h42 : UnipotentWeightIntegrable nuU w (rationalHeight (F := F) ρ) := by
    obtain ⟨ζ, hζ⟩ := (standardCocharacter F G hG S i hi ν hν J hJ).1
    have hζr := hζ.neg i ν (relativeRootNegation F G hG S i hi)
    have hO := oppositeUnipotent_neg_standard_eq hG hi hν hζ
    have hI := hIntegral F G hG S i hi (-ν) hνr (Neg.neg '' J) (-ζ) hζr
      K0 hK0o hK0c hbasisr hcoverr K hKo hPKr hKc N ρ hρ
    rw [hO] at hI
    obtain ⟨d, hd⟩ := hI nuU
    exact ⟨d, hd⟩
  have hRep := constantTermRepresentativeEstimate_of_bounds
    (rationalHeight_nonneg ρ)
    (fun m => (rationalLeviXi_pos hKo hKc hG hi hν hJ hM m).le)
    (fun _ _ => iwasawaWeight_nonneg _) (fun _ => iwasawaWeight_nonneg _) heM h44
    (rationalSigmaProductBound hG hi hν hJ ρ hρ) h11 h42
  exact rationalConstantTermEstimate_of_compact_doubleCosetCover hKo hKc ρ
    hG hi hν hJ hPK hM hK0o hK0c hCoverT nuU hRep

/-- The exact actual constant-term statement follows from the three named
analytic inputs; this proposition does not assert any of those inputs. -/
def RationalConstantTermAnalyticReductionStatement : Prop :=
  RationalXiGlobalUpperBoundStatement.{u} →
    RationalUnipotentWeightIntegrabilityStatement.{u} →
      RationalLeviXiLowerBoundStatement.{u} → RationalConstantTermEstimateStatement.{u}

/-- The complete conditional assembly of the unchanged actual target. -/
theorem rationalConstantTermAnalyticReduction :
    RationalConstantTermAnalyticReductionStatement.{u} :=
  rationalConstantTermEstimate_of_analyticInputs

end Langlands.HarishChandraSchwartz

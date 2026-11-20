import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardSourceConstants
import Langlands.GroupScheme.Dynamic.OppositeParabolicComparison

/-! # Source scalars on a fixed actual semistandard index -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj ENNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel
open Langlands.BruhatTits.DynamicUnipotentContainment

namespace Langlands.HarishChandraSchwartz.RationalSemistandard.SourceConstants

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G}
  {hG : IsConnectedReductive G}

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

/-- At fixed compact normalization, two presentations of the same intrinsic
triple give the same actual gamma, rank-one product and Plancherel constant. -/
theorem eq_of_presentation {p : SemistandardSpectralIndex i}
    (hi : IsMaximalSplitTorus i)
    (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
    (r s : CocharacterPresentation hG p) :
    gamma r K hK = gamma s K hK ∧
    RationalDynamicSource.rankOneGammaProduct i r.cocharacter K hK =
      RationalDynamicSource.rankOneGammaProduct i s.cocharacter K hK ∧
    c r K hK = c s K hK := by
  let := hG.smooth
  have hpar := r.parabolic_eq.trans s.parabolic_eq.symm
  have hlevi := r.levi_eq.trans s.levi_eq.symm
  have hzero (alpha : characterLattice S) (hroot : alpha ∈ relativeRoots i) :
      latticePairing S alpha r.cocharacter = 0 ↔ latticePairing S alpha s.cocharacter = 0 :=
    ⟨root_zero_imp_of_dynamicCentralizer_rationalPoints_le hi.1.1 i r.cocharacter s.cocharacter
      (by rw [hlevi]) hroot,
      root_zero_imp_of_dynamicCentralizer_rationalPoints_le hi.1.1 i s.cocharacter r.cocharacter
        (by rw [hlevi]) hroot⟩
  have hnonneg (alpha : characterLattice S) (hroot : alpha ∈ relativeRoots i) :
      0 ≤ latticePairing S alpha r.cocharacter ↔ 0 ≤ latticePairing S alpha s.cocharacter :=
    ⟨(relativeRootSignInclusions F G hG S i hi r.cocharacter s.cocharacter).1.mp
      (le_of_eq hpar) alpha hroot,
      (relativeRootSignInclusions F G hG S i hi s.cocharacter r.cocharacter).1.mp
        (le_of_eq hpar.symm) alpha hroot⟩
  have hpos : positiveRelativeRoots i r.cocharacter = positiveRelativeRoots i s.cocharacter := by
    ext alpha
    change (_ ∧ _) ↔ (_ ∧ _)
    apply and_congr_right
    intro hroot
    have hn := hnonneg alpha hroot
    have hz := hzero alpha hroot
    omega
  have hzroots : RationalDynamicSource.leviRelativeRoots i r.cocharacter =
      RationalDynamicSource.leviRelativeRoots i s.cocharacter := by
    ext alpha
    exact and_congr_right (hzero alpha)
  have hneg (alpha : characterLattice S) (hroot : alpha ∈ relativeRoots i) :
      0 < latticePairing S alpha (-r.cocharacter) ↔ 0 < latticePairing S alpha (-s.cocharacter) := by
    simpa only [map_neg, neg_pos, not_le] using (hnonneg alpha hroot).not
  have hopp : Dynamic.unipotent (RationalDynamicSource.oppositeCocharacter r.hom) =
      Dynamic.unipotent (RationalDynamicSource.oppositeCocharacter s.hom) := by
    change Dynamic.unipotent (Dynamic.oppositeCocharacter r.hom) =
      Dynamic.unipotent (Dynamic.oppositeCocharacter s.hom)
    rw [← groupHom_neg_comp_eq_oppositeCocharacter i r.cocharacter,
      ← groupHom_neg_comp_eq_oppositeCocharacter i s.cocharacter]
    exact le_antisymm
      ((relativeRootSignInclusions F G hG S i hi (-r.cocharacter) (-s.cocharacter)).2
        fun alpha ha => (hneg alpha ha).mp)
      ((relativeRootSignInclusions F G hG S i hi (-s.cocharacter) (-r.cocharacter)).2
        fun alpha ha => (hneg alpha ha).mpr)
  have hgamma : gamma r K hK = gamma s K hK :=
    RationalDynamicSource.gamma_eq_of_dynamic_subgroups_eq r.hom s.hom K hK hpar hopp
  have hset : RationalDynamicSource.rankOneCocharacterSet i r.cocharacter =
      RationalDynamicSource.rankOneCocharacterSet i s.cocharacter := by
    unfold RationalDynamicSource.rankOneCocharacterSet RationalDynamicSource.rankOneCocharacters
    rw [hpos, hzroots]
  have hproduct : RationalDynamicSource.rankOneGammaProduct i r.cocharacter K hK =
      RationalDynamicSource.rankOneGammaProduct i s.cocharacter K hK := by
    unfold RationalDynamicSource.rankOneGammaProduct
    apply finprod_mem_congr hset
    intro N _
    unfold RationalDynamicSource.rankOneGamma RationalDynamicSource.leviGamma
    symm
    have hN := RationalDynamicSource.isClosed_cocharacterSubmoduleCentralizer i N
    exact compactNormalizedSourceGamma_eq_of_transport (ContinuousMulEquiv.refl _) K K hK hK
      (RationalDynamicSource.isClosed_parabolic_inf r.hom _ hN)
      (RationalDynamicSource.isClosed_oppositeRadical_inf r.hom _ hN)
      (RationalDynamicSource.isClosed_parabolic_inf s.hom _ hN)
      (RationalDynamicSource.isClosed_oppositeRadical_inf s.hom _ hN)
      (fun _ => by simp only [ContinuousMulEquiv.refl_apply, hpar])
      (fun _ => by simp only [ContinuousMulEquiv.refl_apply, hopp, unipotentPoints])
      (fun _ => Iff.rfl)
  refine ⟨hgamma, hproduct, ?_⟩
  change (gamma r K hK)⁻¹ * _ = (gamma s K hK)⁻¹ * _
  rw [hgamma, hproduct]

variable (hi : IsMaximalSplitTorus i)
  (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))

/-- The source gamma attached to the actual index, using dynamic coverage. -/
def gammaAtIndex (hD : SemistandardSpectralDynamicCoverageStatement.{u})
    (p : SemistandardSpectralIndex i) : ℝ≥0∞ :=
  gamma (CocharacterPresentation.ofCoverage hG hD hi p) K hK

/-- The source Plancherel constant attached to the actual index, using dynamic coverage. -/
def cAtIndex (hD : SemistandardSpectralDynamicCoverageStatement.{u})
    (p : SemistandardSpectralIndex i) : ℝ≥0∞ :=
  c (CocharacterPresentation.ofCoverage hG hD hi p) K hK

/-- The index-level gamma agrees with its value in every actual presentation. -/
theorem gammaAtIndex_eq (hD : SemistandardSpectralDynamicCoverageStatement.{u})
    {p : SemistandardSpectralIndex i} (r : CocharacterPresentation hG p) :
    gammaAtIndex (hG := hG) hi K hK hD p = gamma r K hK :=
  (eq_of_presentation hi K hK (CocharacterPresentation.ofCoverage hG hD hi p) r).1

/-- The index-level Plancherel constant agrees with its value in every actual presentation. -/
theorem cAtIndex_eq (hD : SemistandardSpectralDynamicCoverageStatement.{u})
    {p : SemistandardSpectralIndex i} (r : CocharacterPresentation hG p) :
    cAtIndex (hG := hG) hi K hK hD p = c r K hK :=
  (eq_of_presentation hi K hK (CocharacterPresentation.ofCoverage hG hD hi p) r).2.2

end Langlands.HarishChandraSchwartz.RationalSemistandard.SourceConstants

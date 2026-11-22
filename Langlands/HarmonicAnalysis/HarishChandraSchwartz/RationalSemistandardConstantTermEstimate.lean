import Langlands.GroupScheme.Rational.ParabolicRootPresentationExistenceReduction
import Langlands.GroupScheme.Rational.SemistandardSpectralDynamicCoverageProof
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardOrbitSections
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSpecialCompactConstantTermPremises
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalXiChangeMinimal
import Langlands.Representation.Exponents.ArbitraryParabolicLeviPoints

/-! # The normalized constant-term estimate on an actual semistandard parabolic -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Aubert.General Langlands.BruhatTits.SpecialCompact
open Langlands.Aubert.General.RepresentedParabolic (subgroupCongrContinuous)

namespace Langlands.HarishChandraSchwartz.RationalSemistandard

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {S : CommGroupScheme (Spec (CommRingCat.of F))} {i : S.toGrp ⟶ G}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (p : SemistandardSpectralIndex i)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- A generic refinement of the cocharacter presenting the intrinsic triple
makes the same parabolic, Levi and radical standard for its zero face. -/
theorem exists_standard_presentation :
    ∃ (ξ : cocharacterLattice S) (hξ : IsGenericCocharacter i ξ)
      (J : Set (characterLattice S)) (hJ : J ⊆ simpleRelativeRoots i ξ),
        p = SemistandardSpectralIndex.ofStandard hG hi ξ hξ J hJ := by
  obtain ⟨ζ, hζ⟩ := semistandardSpectralDynamicCoverage F G hG S i hi p
  obtain ⟨ξ, hξ, hrefine⟩ := hi.isSplitSubtorus.1.exists_genericCocharacter_refining i ζ
  have hface := isStandardCocharacter_simpleRootFace i ξ (xi := ζ) fun α hα =>
    have hα' := simpleRelativeRoots_subset_positive i ξ hα
    hrefine α hα'.1 hα'.2.le
  refine ⟨ξ, hξ, simpleRootFace i ξ ζ, hface.subset, ?_⟩
  exact hζ.symm.trans
    (SemistandardSpectralIndex.ofStandard_eq_ofCocharacter hG hi ξ hξ _ hface.subset ζ hface).symm

variable {ν ξ : cocharacterLattice S}
  (hξ : IsGenericCocharacter i ξ)
  {J : Set (characterLattice S)} (hJ : J ⊆ simpleRelativeRoots i ξ)
  (hp : p = SemistandardSpectralIndex.ofStandard hG hi ξ hξ J hJ)
  {K : OpenSubgroup (rationalPoints G)}
  (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup)
  (hMK : IsIwasawaPair ((standardParabolicPoints i ξ ∅).subgroupOf (standardLeviPoints i ξ J))
    (K.toSubgroup.subgroupOf (standardLeviPoints i ξ J)))
  {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N))
  (muU : Measure (radical p)) [muU.IsHaarMeasure]

/-- The actual constant-term estimate after changing the ambient minimal
parabolic to a chamber in which the indexed triple is standard. -/
def SemistandardConstantTermEstimateStatement : Prop :=
  IsGenericCocharacter i ν →
    RationalConstantTermEstimateStatement.{u} → JointSpecialCompactBasisExistenceStatement.{u} →
    IsClosedSubgroup ρ →
    ConstantTermEstimate muU
      (HaarModulus.closedRestrictCharacter (radical p) (isClosed_radical p) (levi p)
        (decomposition p).levi_le_normalizer)
      (rationalXi hKc hPK) (rationalHeight (F := F) ρ)
      (rationalLeviXi hKc hMK ∘ subgroupCongrContinuous (congrArg levi hp))
      (fun x => rationalHeight (F := F) ρ (x : rationalPoints G))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
/-- The original ambient Xi is unchanged at the same compact. Apply the
standard result and identify the literal measures and characters. -/
theorem semistandardConstantTermEstimate :
    SemistandardConstantTermEstimateStatement hG hi p hξ hJ hp hKc hPK hMK ρ muU := by
  intro hν hE hJoint hρ
  subst p
  obtain ⟨K0, hK0o, hK0c, _, hbasis, hcover, hLevi⟩ :=
    exists_constantTermPremises_of_joint hJoint hG hi hξ
  have hPKξ := IsIwasawaPair.rationalChangeMinimal hG hi hν hξ hPK
  let mu : Measure (standardUnipotentPoints i ξ J) := muU
  let : mu.IsHaarMeasure := inferInstanceAs muU.IsHaarMeasure
  have h := hE.constantTermEstimate hG hi hξ hJ hK0o hK0c hbasis hcover (hLevi J hJ).1
    K.isOpen hKc hPKξ hMK hρ mu
  have hΞ := funext (rationalXi_changeMinimal hG hi hν hξ K.isOpen hKc hPK hPKξ)
  rw [hΞ] at h
  exact h

end Langlands.HarishChandraSchwartz.RationalSemistandard

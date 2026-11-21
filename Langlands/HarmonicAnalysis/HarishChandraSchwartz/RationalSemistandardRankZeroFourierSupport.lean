import Langlands.GroupScheme.Rational.SemistandardProperLeviRankProof
import Langlands.GroupScheme.Rational.SemistandardSpectralFinitenessProof
import Langlands.GroupScheme.Rational.SemistandardSpectralUniquenessProof
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.FullLeviInduction
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOrbitFinitenessByRank
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardFourierThetaSupport
import Langlands.Representation.Parabolic.LeviInflationAdmissibilityProof

/-! # Finite support of the actual Fourier family in relative rank zero -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Aubert.General Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz.RationalSemistandard

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  [Fintype (RationalPointFamily.SimpleRoot i ν)]
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)

/-- At the full-group endpoint, evaluation at one identifies fixed vectors with
the fixed vectors at the literal Levi level for every subgroup. -/
theorem inducedFixedVectors_ne_bot_iff_of_full
    (p : SemistandardSpectralIndex i) (hP : parabolic p = ⊤)
    (hM : levi p = ⊤) (hU : radical p = ⊥)
    (A : SmoothRep.{0, u, uV} ℂ (levi p)) (H : Subgroup (rationalPoints G)) :
    fixedVectors ((normalizedInductionFunctor (decomposition p) (isClosed_radical p)).obj
      A).representation H ≠ ⊥ ↔ fixedVectors A.representation (leviLevel p H) ≠ ⊥ := by
  let e := fullLeviGroupEquiv (levi p) hM
  have hlevel : H.map e.toMonoidHom = leviLevel p H := by
    ext x
    rw [Subgroup.mem_map, mem_leviLevel]
    constructor
    · rintro ⟨g, hg, rfl⟩
      change (e g : rationalPoints G) ∈ H
      rwa [coe_fullLeviGroupEquiv]
    · intro hx
      refine ⟨x.val, hx, Subtype.ext ?_⟩
      exact coe_fullLeviGroupEquiv (levi p) hM x.val
  have h := fixedVectors_ne_bot_iff_of_equiv
    (fullLeviInductionEquiv (decomposition p) (isClosed_radical p) hP hM hU A) H
  change _ ↔ fixedVectors (A.representation.comp e.toMonoidHom) H ≠ ⊥ at h
  rwa [fixedVectors_comp_eq_map, hlevel] at h

include hG hi hν in
/-- The forward fixed-level comparison across all semistandard indices in
rank zero. Every index then coincides with the full standard one. -/
theorem normalLevelFixedComparison_of_rank_zero
    (hzero : relativeRootRank i = 0) (K : OpenSubgroup (rationalPoints G)) :
    RationalSemistandardNormalLevelFixedComparison.{u, uV} (i := i) K := by
  intro p
  let pG := standardIndex hG hi hν Finset.univ
  have hp : p = pG := by
    apply semistandardSpectralUniqueness F G hG S i hi
    apply Subtype.ext
    change p.parabolic = standardParabolic i ν (RationalPointFamily.rootSet i ν Finset.univ)
    rw [semistandardParabolic_eq_top_of_rank_zero semistandardProperLeviRank hG hi hzero p,
      RationalPointFamily.rootSet_univ]
    have hfull := (standardCocharacter F G hG S i hi ν hν _ Set.Subset.rfl).2
      0 (isStandardCocharacter_simple_zero i ν)
    rw [hfull.1, groupHom_zero_comp_eq_trivialCocharacter, Dynamic.parabolic_trivialCocharacter]
  subst p
  intro H _ _ A h
  exact (inducedFixedVectors_ne_bot_iff_of_full pG
    (RationalPointFamily.parabolic_univ_eq_top i ν standardCocharacter hG hi hν)
    (RationalPointFamily.levi_univ_eq_top i ν standardCocharacter hG hi hν)
    (RationalPointFamily.unipotent_univ_eq_bot i ν) A H.toSubgroup).mp h

variable {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup)
  {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N))
  {muG : Measure (rationalPoints G)} [muG.IsMulLeftInvariant] [muG.IsMulRightInvariant]
  (hsw : SquareIntegrableWeight muG (rationalXi hKc hPK) (rationalHeight (F := F) ρ))
  {T : SemistandardSpectralIndex i → CommGroupScheme (Spec (CommRingCat.of F))}
  (a : ∀ p, (T p).toGrp ⟶ (chosenLeviModel p).scheme)
  (ha : ∀ p, IsSplitComponent (a p))
  [∀ p, ((chosenLeviModel p).splitCenter (a p)).Normal]
  [∀ p, MeasurableSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))]
  [∀ p, BorelSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))]
  (muM : ∀ p, Measure (levi p ⧸ (chosenLeviModel p).splitCenter (a p)))
  [∀ p, (muM p).IsHaarMeasure] [∀ p, (muM p).IsInvInvariant]
  (d : ∀ p : SemistandardSpectralIndex i, CompactData p)
  (hdelta : ∀ p : SemistandardSpectralIndex i, ModularNormalization p)
  (hT : ∀ (p : SemistandardSpectralIndex i)
    (A : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p)),
    IsSquareIntegrableModCentralSubgroup ((chosenLeviModel p).splitCenter (a p))
      ((chosenLeviModel p).splitCenter_le_center (a p) (ha p)) A.obj.representation (muM p) →
    HasTemperedCoefficients (rationalXi hKc hPK) (rationalHeight (F := F) ρ)
      ((normalizedInductionFunctor (decomposition p) (isClosed_radical p)).obj A.obj).representation)

/-- The rank-zero VIII.1.2 result suffices for finite support of the actual
rank-zero Fourier family. -/
def RankZeroFourierFiniteSupportStatement : Prop :=
  RationalRankZeroDiscreteSeriesOrbitFinitenessStatement.{u, uV} →
    relativeRootRank i = 0 →
    RationalSemistandardFourierFiniteSupportStatement hG hi hν hKc hPK ρ hsw a ha muM d hdelta hT

/-- Apply the fixed-orbit counting theorem with the bound one and the
comparison at the full-group endpoint. -/
theorem rankZeroFourierFiniteSupport :
    RankZeroFourierFiniteSupportStatement hG hi hν hKc hPK ρ hsw a ha muM d hdelta hT := by
  intro hfin hzero
  apply rationalSemistandardFourierFiniteSupport_of_fixedFinite hG hi hν hKc hPK ρ hsw
    a ha muM d hdelta hT
  exact finite_rationalSemistandardThetaFixed a ha muM K hKc
    (semistandardSpectralFiniteness F G hG S i hi)
    (normalLevelFixedComparison_of_rank_zero hG hi hν hzero K)
    (allLeviOrbitFiniteness_of_rank_lt hG hi
      (rationalStrictlyLowerRankOrbitFiniteness_one_iff.mpr hfin) (hzero.symm ▸ Nat.zero_lt_one))

end Langlands.HarishChandraSchwartz.RationalSemistandard

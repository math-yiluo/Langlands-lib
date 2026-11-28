import Langlands.GroupScheme.Rational.CocharacterStandardFace
import Langlands.GroupScheme.Rational.StandardParabolicClassificationProof
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalConstantTermEstimateProof
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCuspidalConvergenceReductions
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCuspidalSemistandardComparison
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOppositeCuspidality
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardConstantTermEstimate
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardSourceConstants
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSpecialPacketCompact
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakExpansionSpecialCompact
import Langlands.Representation.Aubert.General.RepresentedStandardCuspidality

/-! # Cuspidal constant terms on the whole semistandard index

This module proves `RationalCuspidalSemistandardComparisonStatement`. A proper
member of the full semistandard index is an inner conjugate of a proper
standard face, so the standard integrable kernel transports to it. Conversely,
each proper standard face is a member of the index, and the standard radical
estimate of Waldspurger II.4.5 supplies the convergence. -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.BruhatTits.SpecialCompact Langlands.GroupScheme

namespace Langlands.HarishChandraSchwartz

open RationalSemistandard

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
/-- Apply the standard radical estimate at a special packet compact and
transport the Schwartz bound from the prescribed Iwasawa compact. -/
private theorem standardConstantTermConvergence :
    RationalSchwartzConstantTermConvergenceStatement.{u} := by
  intro F _ _ _ _ G _ _ hG S i hi ν hν K hK hPK N _ ρ hρ f I _ μU _ x y
  obtain ⟨L, hL, hVertex, hProducts, hbasis, hcover, hLeviCover⟩ := hasSpecialPacketCompact hi ν hG hν
  have hLspec : SpecialCompactProperties F i ν L.toSubgroup := by
    obtain ⟨_, D, _, _, z, _, hz, hLz⟩ := hVertex
    exact hLz ▸ hz
  have hPL : IsIwasawaPair (standardParabolicPoints i ν ∅) L.toSubgroup :=
    isIwasawaPair_of_pointProductEqualities (hProducts.2.2.1 ∅ (Set.empty_subset _))
  let J := rootSet i ν I
  have hJ := rootSet_subset i ν I
  have hML := standardLeviIwasawaFactorsAt_of_factorization hG hi hν L.toSubgroup hPL
    hLspec.2.2.2 J hJ
  exact rationalConstantTermEstimate.integrable_mul_mul hG hi hν hJ L.isOpen hL hbasis hcover
    (hLeviCover J hJ) L.isOpen hL hPL hML K.isOpen hK hPK hρ μU (Space.coe_mem f) x y

section StandardConjugation

variable {F : Type u} [Field F] {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} {i : S.toGrp ⟶ G} [IsAffineHom G.X.hom]
  {ν : cocharacterLattice S} [Fintype (SimpleRoot i ν)]

private theorem exists_rootSet_eq_of_subset {J : Set (characterLattice S)}
    (hJ : J ⊆ simpleRelativeRoots i ν) : ∃ I : Finset (SimpleRoot i ν), rootSet i ν I = J := by
  classical
  refine ⟨Finset.univ.filter (fun α => (α : characterLattice S) ∈ J), ?_⟩
  ext α
  constructor
  · rintro ⟨β, hβ, rfl⟩
    exact (Finset.mem_filter.mp hβ).2
  · intro hα
    exact ⟨⟨α, hJ hα⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hα⟩, rfl⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1200000 in
private theorem exists_standardRadical_comap (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (p : SemistandardSpectralIndex i) (hp : p.parabolic ≠ ⊤) :
    ∃ (I : Finset (SimpleRoot i ν)) (g : rationalPoints G),
      rootSet i ν I ≠ simpleRelativeRoots i ν ∧
        p.radical = (standardUnipotent i ν (rootSet i ν I)).comap (G.innerIso g).hom := by
  let r := CocharacterPresentation.ofCoverage hG semistandardSpectralDynamicCoverage hi p
  obtain ⟨g, ξ, hg, hle⟩ := exists_innerIso_comp_eq_dominant_cocharacter hG hi hν r.hom
  let J := simpleRootFace i ν ξ
  have hJ : J ⊆ simpleRelativeRoots i ν := simpleRootFace_subset i ν ξ
  have hξ : IsStandardCocharacter i ν J ξ := isStandardCocharacter_simpleRootFace i ν fun α hα =>
    (relativeRootSignInclusions F G hG S i hi ν ξ).1.mp hle α
      (simpleRelativeRoots_subset_positive i ν hα).1
      (simpleRelativeRoots_subset_positive i ν hα).2.le
  obtain ⟨I, hI⟩ := exists_rootSet_eq_of_subset hJ
  obtain ⟨_, hcompare⟩ := standardCocharacter F G hG S i hi ν hν J hJ
  obtain ⟨hPstd, _, hUstd⟩ := hcompare ξ hξ
  have hP : p.parabolic = (standardParabolic i ν J).comap (G.innerIso g).hom := by
    rw [← r.parabolic_eq, hPstd, ← hg]
    exact Dynamic.parabolic_eq_comap_of_iso r.hom (G.innerIso g)
  refine ⟨I, g, ?_, ?_⟩
  · intro h
    apply hp
    rw [hP, ← hI, h, standardParabolic_simple_eq_top_of_relativeRootNegation relativeRootNegation
      F G hG S i hi ν hν, SubgroupFunctor.comap_top]
  · rw [← r.radical_eq, hI, hUstd, ← hg]
    exact Dynamic.unipotent_eq_comap_of_iso r.hom (G.innerIso g)

end StandardConjugation

private theorem integrableCuspidal_of_comap_inner
    {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [MeasurableSpace Γ] [BorelSpace Γ] {U V : Subgroup Γ}
    (g : Γ) (hV : V = U.comap (MulAut.conj g).toMonoidHom) {f : Γ → ℂ}
    (hf : ∀ measure : Measure U, measure.IsHaarMeasure → IsIntegrableUnipotentCuspidal measure f)
    (measure : Measure V) [measure.IsHaarMeasure] :
    IsIntegrableUnipotentCuspidal measure f := by
  have hConj (x : Γ) : g⁻¹ * x * (g⁻¹)⁻¹ ∈ V ↔ x ∈ U := by
    rw [hV, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show g * (g⁻¹ * x * (g⁻¹)⁻¹) * g⁻¹ = x by group]
  let e := conjugationSubgroupContinuousMulEquiv g⁻¹ hConj
  exact isIntegrableUnipotentCuspidal_of_conjugation g⁻¹ e (fun _ => rfl) hf measure

section IntegralComparison

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} {i : S.toGrp ⟶ G}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {ν : cocharacterLattice S} {K : OpenSubgroup (rationalPoints G)}
  {hK : IsCompact (K : Set (rationalPoints G))}
  {hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup}
  {N : ℕ} [Nonempty (Fin N)] {ρ : MatrixRepresentation G (Fin N)}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (f : RationalSchwartzSpace hK hPK ρ)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 650000 in
include hG hi hν in
private theorem semistandardVanish_of_cuspidal
    (hf : f ∈ rationalCuspidalSubmodule hK hPK ρ) :
    RationalSemistandardConstantTermsVanish (i := i) f := by
  intro p hp μV hμV
  let := hμV
  let : Fintype (SimpleRoot i ν) := (hi.isSplitSubtorus.1.finite_simpleRelativeRoots i ν).fintype
  obtain ⟨I, g, hproper, hRad⟩ := exists_standardRadical_comap hG hi hν p hp
  have hRadPoints : radical p =
      (standardUnipotentPoints i ν (rootSet i ν I)).comap (MulAut.conj g).toMonoidHom :=
    (congrArg SubgroupFunctor.rationalPoints hRad).trans
      (SubgroupFunctor.rationalPoints_comap_innerIso_hom _ g)
  have hstandard : ∀ measure : Measure (standardUnipotentPoints i ν (rootSet i ν I)),
      measure.IsHaarMeasure → IsIntegrableUnipotentCuspidal measure (f : rationalPoints G → ℂ) :=
    (mem_rationalCuspidalSubmodule hK hPK ρ f).mp hf I hproper
  have hV := integrableCuspidal_of_comap_inner g hRadPoints hstandard μV
  exact ((isIntegrableUnipotentCuspidal_iff_semistandardConstantTermInd p μV _).mp hV).2

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1400000 in
include hG hi hν in
private theorem cuspidal_of_semistandardVanish (hρ : IsClosedSubgroup ρ)
    (hf : RationalSemistandardConstantTermsVanish (i := i) f) :
    f ∈ rationalCuspidalSubmodule hK hPK ρ := by
  apply (mem_rationalCuspidalSubmodule_iff_constantTermInd hK hPK ρ f).mpr
  intro I hI μU hμU
  let : Fintype (SimpleRoot i ν) := (hi.isSplitSubtorus.1.finite_simpleRelativeRoots i ν).fintype
  let : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
  let := hG.smooth
  have hRoots := relativeRootSystemStatement_of_rootRankOneFactorizationStatement
    rootRankOneFactorization F G hG S i hi
  let J := rootSet i ν I
  have hJ := rootSet_subset i ν I
  let p := SemistandardSpectralIndex.ofStandard hG hi ν hν J hJ
  have hproper : p.parabolic ≠ ⊤ := standardParabolic_ne_top_of_ne_univ i ν
    hi.isSplitSubtorus.1 hRoots standardCocharacter hG hi hν
    (fun he => hI (he ▸ rootSet_univ i ν))
  let := hμU
  exact ⟨standardConstantTermConvergence F G hG S i hi ν hν K hK hPK N ρ hρ f I hI μU,
    hf p hproper μU hμU⟩

end IntegralComparison

/-- The standard integral kernel and full semistandard normalized vanishing
agree on the actual Schwartz space. -/
theorem rationalCuspidalSemistandardComparison : RationalCuspidalSemistandardComparisonStatement.{u} := by
  intro F _ _ _ _ G _ _ hG S i hi ν hν K hK hPK N _ ρ hρ f
  exact ⟨semistandardVanish_of_cuspidal hG hi hν f, cuspidal_of_semistandardVanish hG hi hν f hρ⟩

end Langlands.HarishChandraSchwartz

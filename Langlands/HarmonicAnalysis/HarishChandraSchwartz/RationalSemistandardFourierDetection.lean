import Langlands.GroupScheme.Rational.SemistandardProperLeviRankProof
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardConstantTermHaar
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardCuspidalFourierVanishing
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardLeviFourierVanishing

/-! # The local input for Fourier detection on a proper Levi -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz

open RationalSemistandard

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G}

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

local instance detectionLeviAffine {p : SemistandardSpectralIndex i} (m : LeviModel p) :
    IsAffineHom m.scheme.X.hom := m.reductive.isAffineHom

local instance detectionLeviFiniteType {p : SemistandardSpectralIndex i} (m : LeviModel p) :
    LocallyOfFiniteType m.scheme.X.hom := by
  let := m.reductive.smooth
  infer_instance

local instance detectionCompactOpen {H : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom] :
    Nonempty (CompactOpenSubgroup (rationalPoints H)) :=
  ⟨Langlands.BruhatTits.rationalPointCompactOpenSubgroup F H⟩

variable {nu : cocharacterLattice S}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (hnu : IsGenericCocharacter i nu)
  {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i nu ∅) (K : Subgroup (rationalPoints G)))
  {N : ℕ} [Nonempty (Fin N)] (rho : MatrixRepresentation G (Fin N))
  {muG : Measure (rationalPoints G)} [muG.IsMulLeftInvariant] [muG.IsMulRightInvariant]
  (hsw : SquareIntegrableWeight muG (rationalXi hKc hPK) (rationalHeight (F := F) rho))
  {T : SemistandardSpectralIndex i → CommGroupScheme (Spec (CommRingCat.of F))}
  (a : ∀ r, (T r).toGrp ⟶ (chosenLeviModel r).scheme)
  (ha : ∀ r, IsSplitComponent (a r))
  [∀ r, ((chosenLeviModel r).splitCenter (a r)).Normal]
  [∀ r, MeasurableSpace (levi r ⧸ (chosenLeviModel r).splitCenter (a r))]
  [∀ r, BorelSpace (levi r ⧸ (chosenLeviModel r).splitCenter (a r))]
  (muR : ∀ r, Measure (levi r ⧸ (chosenLeviModel r).splitCenter (a r)))
  [∀ r, (muR r).IsHaarMeasure] [∀ r, (muR r).IsInvInvariant]
  (d : ∀ r : SemistandardSpectralIndex i, CompactData r)
  (hdelta : ∀ r : SemistandardSpectralIndex i, ModularNormalization r)
  (hT : ∀ (r : SemistandardSpectralIndex i)
    (A : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi r)),
    IsSquareIntegrableModCentralSubgroup ((chosenLeviModel r).splitCenter (a r))
      ((chosenLeviModel r).splitCenter_le_center (a r) (ha r)) A.obj.representation (muR r) →
    HasTemperedCoefficients (rationalXi hKc hPK) (rationalHeight (F := F) rho)
      ((normalizedInductionFunctor (decomposition r) (isClosed_radical r)).obj A.obj).representation)

/-- Data on one actual outer Levi for the nested VII.1.2 calculation.
The ambient Fourier parameters in `coverage` are shared with the cutoff.
The field `radicalHaar` works at every translating pair on this Levi. -/
structure RationalSemistandardLeviFourierData (p : SemistandardSpectralIndex i) where
  model : LeviModel p
  torus : CommGroupScheme (Spec (CommRingCat.of F))
  iM : torus.toGrp ⟶ model.scheme
  maximal : IsMaximalSplitTorus iM
  nuM : cocharacterLattice torus
  generic : IsGenericCocharacter iM nuM
  compact : OpenSubgroup (rationalPoints model.scheme)
  compact_isCompact : IsCompact (compact : Set (rationalPoints model.scheme))
  iwasawa : IsIwasawaPair (standardParabolicPoints iM nuM ∅)
    (compact : Subgroup (rationalPoints model.scheme))
  ambientHaar : Measure (rationalPoints model.scheme)
  [ambientHaar_haar : ambientHaar.IsHaarMeasure]
  [ambientHaar_right : ambientHaar.IsMulRightInvariant]
  squareIntegrableWeight : SquareIntegrableWeight ambientHaar (rationalXi compact_isCompact iwasawa)
    (rationalHeight (F := F) (rho.restrict model.inclusion))
  xi : levi p → ℝ
  height : levi p → ℝ
  xi_eq : ∀ x, rationalXi compact_isCompact iwasawa x = xi (model.pointHomeomorph x)
  height_eq : ∀ x, rationalHeight (F := F) (rho.restrict model.inclusion) x =
    height (model.pointHomeomorph x)
  radicalHaar : Measure (radical p)
  [radicalHaar_haar : radicalHaar.IsHaarMeasure]
  [radicalHaar_sfinite : SFinite radicalHaar]
  constantTermData : ConstantTermData radicalHaar (semistandardUnipotentModulus p)
  constantTermEstimate : ConstantTermEstimate radicalHaar (semistandardUnipotentModulus p)
    (rationalXi hKc hPK) (rationalHeight (F := F) rho) xi height
  translations : TranslationWeights xi height
  conjugationModulus : IsConjModulus (semistandardLeviPoints_le_normalizer_radicalPoints p)
    radicalHaar (semistandardUnipotentModulus p)
  splitCenterTorus : SemistandardSpectralIndex iM → CommGroupScheme (Spec (CommRingCat.of F))
  splitCenterInclusion : ∀ q, (splitCenterTorus q).toGrp ⟶ (chosenLeviModel q).scheme
  splitComponent : ∀ q, IsSplitComponent (splitCenterInclusion q)
  [centerNormal : ∀ q, ((chosenLeviModel q).splitCenter (splitCenterInclusion q)).Normal]
  [quotientMeasurable : ∀ q, MeasurableSpace (levi q ⧸
    (chosenLeviModel q).splitCenter (splitCenterInclusion q))]
  [quotientBorel : ∀ q, BorelSpace (levi q ⧸
    (chosenLeviModel q).splitCenter (splitCenterInclusion q))]
  quotientHaar : ∀ q, Measure (levi q ⧸ (chosenLeviModel q).splitCenter (splitCenterInclusion q))
  [quotientHaar_haar : ∀ q, (quotientHaar q).IsHaarMeasure]
  [quotientHaar_inv : ∀ q, (quotientHaar q).IsInvInvariant]
  compactData : ∀ q : SemistandardSpectralIndex iM, CompactData q
  normalization : ∀ q : SemistandardSpectralIndex iM, ModularNormalization q
  tempered : ∀ (q : SemistandardSpectralIndex iM)
    (A : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi q)),
    IsSquareIntegrableModCentralSubgroup ((chosenLeviModel q).splitCenter (splitCenterInclusion q))
      ((chosenLeviModel q).splitCenter_le_center (splitCenterInclusion q) (splitComponent q))
      A.obj.representation (quotientHaar q) →
    HasTemperedCoefficients (rationalXi compact_isCompact iwasawa)
      (rationalHeight (F := F) (rho.restrict model.inclusion))
      ((normalizedInductionFunctor (decomposition q) (isClosed_radical q)).obj A.obj).representation
  coverage : RationalSemistandardNestedFourierCoverage.{u, uV}
    (muG := muG) (muLevi := ambientHaar) hKc hPK rho p model compact_isCompact iwasawa
    radicalHaar a ha muR d splitCenterInclusion splitComponent quotientHaar compactData

namespace RationalSemistandardLeviFourierData

attribute [local instance] ambientHaar_haar ambientHaar_right radicalHaar_haar radicalHaar_sfinite
  centerNormal quotientMeasurable quotientBorel quotientHaar_haar quotientHaar_inv

variable {hKc hPK rho a ha muR d} {p : SemistandardSpectralIndex i}
  (c : RationalSemistandardLeviFourierData.{u, uV} (muG := muG) hKc hPK rho a ha muR d p)

omit [muG.IsMulLeftInvariant] [muG.IsMulRightInvariant] in
/-- The chosen actual outer Levi has strictly smaller relative rank. -/
theorem rank_lt (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (hp : p.IsProper) :
    relativeRootRank c.iM < relativeRootRank i :=
  relativeRootRank_properLevi_lt semistandardProperLeviRank hG hi p hp c.model.represents
    c.model.closed c.model.reductive c.iM c.maximal

/-- The actual Schwartz function `f^M` used in VIII.2.1. -/
def constantTerm (f : RationalSchwartzSpace hKc hPK rho) (g : rationalPoints G × rationalPoints G) :
    RationalSchwartzSpace c.compact_isCompact c.iwasawa (rho.restrict c.model.inclusion) :=
  rationalSemistandardLeviConstantTerm hKc hPK rho p c.model c.compact_isCompact c.iwasawa
    c.xi_eq c.height_eq c.radicalHaar c.constantTermData c.constantTermEstimate c.translations f g

/-- The full Fourier transform on the actual Schwartz space of the Levi. -/
def fourier :
    RationalSchwartzSpace c.compact_isCompact c.iwasawa (rho.restrict c.model.inclusion) →ₗ[ℂ]
      RationalSemistandardThetaSections.{u, uV}
        c.splitCenterInclusion c.splitComponent c.quotientHaar :=
  rationalSemistandardFourierFamily c.model.reductive c.maximal c.generic c.compact_isCompact
    c.iwasawa (rho.restrict c.model.inclusion) c.squareIntegrableWeight c.splitCenterInclusion
    c.splitComponent c.quotientHaar c.compactData c.normalization c.tempered

set_option maxHeartbeats 1200000 in
/-- For the actual reconstruction input, every Levi Fourier component of
`f^M` vanishes if the proper Fourier truncation of `f` vanishes. -/
theorem fourier_constantTerm_eq_zero (hp : p.IsProper)
    (f : RationalSchwartzSpace hKc hPK rho) (g : rationalPoints G × rationalPoints G)
    (hf : rationalSemistandardProperFourier hG hi hnu hKc hPK rho hsw a ha muR d hdelta hT f = 0) :
    c.fourier (c.constantTerm f g) = 0 :=
  rationalSemistandardLeviFourierVanishing hG hi hnu hKc hPK rho hsw p c.model c.maximal c.generic
    c.compact_isCompact c.iwasawa c.squareIntegrableWeight c.xi_eq c.height_eq c.radicalHaar
    c.constantTermData c.constantTermEstimate c.translations a ha muR d hdelta hT c.splitCenterInclusion
    c.splitComponent c.quotientHaar c.compactData c.normalization c.tempered
    hp c.coverage c.conjugationModulus f g hf

omit [muG.IsMulLeftInvariant] [muG.IsMulRightInvariant] in
/-- Zero in the actual Schwartz model is zero at the chosen radical Haar
on the literal Levi, for the indicated translating pair. -/
theorem constantTerm_eq_zero_iff
    (f : RationalSchwartzSpace hKc hPK rho) (g : rationalPoints G × rationalPoints G) :
    c.constantTerm f g = 0 ↔
      constantTermInd c.radicalHaar (semistandardUnipotentModulus p) f g = 0 :=
  rationalSemistandardLeviConstantTerm_eq_zero_iff hKc hPK rho p c.model
    c.compact_isCompact c.iwasawa c.xi_eq c.height_eq c.radicalHaar c.constantTermData
    c.constantTermEstimate c.translations f g

end RationalSemistandardLeviFourierData

variable {hKc hPK rho a ha muR d}

omit [muG.IsMulLeftInvariant] [muG.IsMulRightInvariant] in
/-- Vanishing in the actual models of the proper Levis gives membership in
the intrinsic kernel by the fixed-Haar normalization comparison. -/
theorem rationalCuspidal_of_properLeviConstantTerms_eq_zero
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (hnu : IsGenericCocharacter i nu)
    (hcompare : RationalCuspidalSemistandardComparisonStatement.{u})
    (hrho : IsClosedSubgroup rho)
    (c : ∀ p : SemistandardSpectralIndex i, p.IsProper →
      RationalSemistandardLeviFourierData.{u, uV} (muG := muG) hKc hPK rho a ha muR d p)
    (f : RationalSchwartzSpace hKc hPK rho)
    (hzero : ∀ p hp g, (c p hp).constantTerm f g = 0) :
    f ∈ rationalCuspidalSubmodule hKc hPK rho := by
  apply rationalSemistandardCuspidalFromConstantTermHaar hKc hPK rho hG hi hnu hcompare hrho f
  intro p hp
  let cp := c p hp
  exact ⟨cp.radicalHaar, cp.radicalHaar_haar, fun g =>
    (cp.constantTerm_eq_zero_iff f g).mp (hzero p hp g)⟩

set_option maxHeartbeats 1800000 in
/-- Fourier detection reduces to the zero case of reconstruction in each
actual strictly lower-rank Levi model. -/
theorem rationalSemistandardProperFourier_eq_zero_iff_mem_cuspidal
    (hcompare : RationalCuspidalSemistandardComparisonStatement.{u})
    (hrho : IsClosedSubgroup rho)
    (hin : ∀ (t : RationalSemistandardTheta.{u, uV} a ha muR), t.1.IsProper →
      ∃ (muL : Measure (levi t.1)) (muU : Measure (radical t.1)) (XiM sigmaM : levi t.1 → ℝ),
        muU.IsHaarMeasure ∧
          RationalSemistandardFourierAnalyticInputs (muG := muG) hKc hPK rho
            t.1 (chosenLeviModel t.1) (d t.1)
            (orbitRepresentative (chosenLeviModel t.1) (a t.1) (ha t.1) (muR t.1) t.2)
            muL muU XiM sigmaM)
    (c : ∀ p : SemistandardSpectralIndex i, p.IsProper →
      RationalSemistandardLeviFourierData.{u, uV} (muG := muG) hKc hPK rho a ha muR d p)
    (hreconstructZero : ∀ p hp, relativeRootRank (c p hp).iM < relativeRootRank i →
      ∀ fM, (c p hp).fourier fM = 0 → fM = 0)
    (f : RationalSchwartzSpace hKc hPK rho) :
    rationalSemistandardProperFourier hG hi hnu hKc hPK rho hsw a ha muR d hdelta hT f = 0 ↔
      f ∈ rationalCuspidalSubmodule hKc hPK rho := by
  constructor
  · intro hf
    apply rationalCuspidal_of_properLeviConstantTerms_eq_zero hG hi hnu hcompare hrho c f
    intro p hp g
    exact hreconstructZero p hp ((c p hp).rank_lt hG hi hp) ((c p hp).constantTerm f g)
      ((c p hp).fourier_constantTerm_eq_zero hG hi hnu hsw hdelta hT hp f g hf)
  · intro hf
    apply (rationalSemistandardProperFourier_eq_zero_iff
      hG hi hnu hKc hPK rho hsw a ha muR d hdelta hT f).mpr
    exact rationalSemistandardCuspidalProperFourierVanishing hG hi hnu hKc hPK rho hsw
      a ha muR d hdelta hT hcompare hrho hin f hf

end Langlands.HarishChandraSchwartz

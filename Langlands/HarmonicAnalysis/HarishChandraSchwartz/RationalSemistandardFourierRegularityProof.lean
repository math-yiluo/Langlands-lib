import Langlands.HarmonicAnalysis.HarishChandraSchwartz.FourierOrbitContinuity
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.OrbitSectionFixedTensor
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardFourierFamily

/-!
# Regularity of the actual semistandard Fourier components

This module proves the four regularity propositions of
`RationalSemistandardFourierFamily` (Waldspurger, VII.1.3): the component map is
continuous for the Schwartz topology and the VI.3 section topology, every
component is a coherent smooth orbit section, a bi-invariant Schwartz function
has its section in the same fixed level and in every smaller level with all
compact restrictions in one finite-dimensional space, and every component of
the full dependent Fourier product is smooth.
-/

noncomputable section

set_option maxRecDepth 4096

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal ComplexConjugate
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz

/- The variable blocks below repeat those of `RationalSemistandardFourierFamily`
in the same order, so that each theorem has exactly the binders of its statement. -/
variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G}

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

open RationalSemistandard

variable {nu : cocharacterLattice S}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hnu : IsGenericCocharacter i nu)
  {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i nu ∅) (K : Subgroup (rationalPoints G)))
  {N : ℕ} [Nonempty (Fin N)] (rho : MatrixRepresentation G (Fin N))
  {muG : Measure (rationalPoints G)} [muG.IsMulLeftInvariant] [muG.IsMulRightInvariant]
  (hsw : SquareIntegrableWeight muG (rationalXi hKc hPK) (rationalHeight (F := F) rho))

local instance regularityAmbientCompactOpen : Nonempty (CompactOpenSubgroup (rationalPoints G)) :=
  ⟨Langlands.BruhatTits.rationalPointCompactOpenSubgroup F G⟩

local instance regularityParabolicLocallyCompact (p : SemistandardSpectralIndex i) :
    LocallyCompactSpace (parabolic p) :=
  (isClosed_parabolic p).locallyCompactSpace

section Component

variable (p : SemistandardSpectralIndex i) (m : LeviModel p) (d : CompactData p)
  (hdelta : ModularNormalization p)
  (pi : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p))
  (C : Subgroup (levi p)) [C.Normal] (hC : C ≤ Subgroup.center (levi p))
  [MeasurableSpace (levi p ⧸ C)] [BorelSpace (levi p ⧸ C)]
  (muM : Measure (levi p ⧸ C)) [muM.IsHaarMeasure] [muM.IsInvInvariant]
  (hsqPi : IsSquareIntegrableModCentralSubgroup C hC pi.obj.representation muM)
  (hT : ∀ A : UnitaryOrbitRepresentative m.normCharacters pi,
    HasTemperedCoefficients (rationalXi hKc hPK) (rationalHeight (F := F) rho)
      ((normalizedInductionFunctor (decomposition p) (isClosed_radical p)).obj A.val.obj).representation)

variable (muL : Measure (levi p)) (muU : Measure (radical p))
  (XiM sigmaM : levi p → ℝ)

set_option maxHeartbeats 2000000 in
/-- The generic Laurent-coordinate theorem produces a continuous map for
the precise semistandard weights, measures and inducing representatives. -/
theorem rationalSemistandardFourierContinuity :
    RationalSemistandardFourierContinuityStatement hG hi hnu hKc hPK rho hsw p m d hdelta
      pi C hC muM hsqPi hT muL muU XiM sigmaM := by
  intro hin
  let : muG.IsInvInvariant := hin.ambient_inv
  let : SigmaFinite muG := hin.ambient_sigmaFinite
  let : muL.IsMulLeftInvariant := hin.levi_left
  let : muL.IsMulRightInvariant := hin.levi_right
  let : muL.IsInvInvariant := hin.levi_inv
  let : SFinite muL := hin.levi_sfinite
  let : muU.IsMulLeftInvariant := hin.radical_left
  let : muU.IsMulRightInvariant := hin.radical_right
  let : SFinite muU := hin.radical_sfinite
  obtain ⟨H, hHc, _⟩ := compactOpenCofinal p d ⊤
  let : Nonempty (CompactOpenSubgroup (levi p)) := ⟨⟨H, hHc⟩⟩
  obtain ⟨B, hB⟩ := hin.laurent_height
  refine ⟨fourierOrbitLaurentSectionCLM
    (decomposition p) (isClosed_radical p) (isClosed_parabolic p)
    d.projection_continuous d.compact d.isCompact d.factorization_mem
    (fun g => RationalPointFamily.rationalReductiveUnimodularity F G hG standardCocharacter g)
    hdelta m.normCharacters pi (compactOpenCofinal p d) C hC muM
    (unitaryOrbitRepresentative_isDiscreteSeries m.normCharacters pi C hC muM hsqPi)
    (rationalL2Weights K.isOpen hKc hPK rho hsw) hT
    (rationalXi_inv hG hi hnu K.isOpen hKc hPK) (rationalHeight_inv rho)
    m.unitaryCoordinates.toMulEquiv m.continuous_normCharacters d.factorization hsqPi
    hin.ambient_compact_volume hin.radical_unimodular hin.levi_weights hin.levi_tempered
    hin.orbit_tempered hin.levi_xi_inv hin.levi_height_inv hin.constant_term
    hin.conjugation_modulus hin.constant_term_estimate
    (rationalTranslationWeights K.isOpen hKc hPK rho) hin.levi_translations
    hin.compact_factorization hin.levi_compact_volume hin.radical_compact_volume
    hin.double_integrability m.unitaryCoordinates_hasLaurent hB, fun f => ?_⟩
  rfl

/-- The continuous map takes values in the actual coherent smooth sections. -/
theorem rationalSemistandardFourierSmoothness :
    RationalSemistandardFourierSmoothnessStatement hG hi hnu hKc hPK rho hsw p m d hdelta
      pi C hC muM hsqPi hT muL muU XiM sigmaM := by
  intro hin f
  obtain ⟨L, hL⟩ := rationalSemistandardFourierContinuity hG hi hnu hKc hPK rho hsw p m d
    hdelta pi C hC muM hsqPi hT muL muU XiM sigmaM hin
  rw [← hL f]
  exact (OrbitSectionSpace.toSections m.normCharacters pi m.unitaryCoordinates.toMulEquiv
    (decomposition p) (isClosed_radical p) d.compact (isClosed_parabolic p) d.isCompact
    m.continuous_normCharacters d.projection_continuous d.factorization (L f)).property

set_option hygiene false in
local notation "SectionLevel" H =>
  orbitSectionLevelSubmodule m.normCharacters pi m.unitaryCoordinates.toMulEquiv
    (decomposition p) (isClosed_radical p) d.compact (isClosed_parabolic p) d.isCompact
    m.continuous_normCharacters d.projection_continuous d.factorization H

set_option maxHeartbeats 2000000 in
/-- Bi-invariance of the function gives the same level for its Fourier section.
Its compact coordinates all lie in a single finite-dimensional submodule. -/
theorem rationalSemistandardFourierCompactLevel :
    RationalSemistandardFourierCompactLevelStatement hG hi hnu hKc hPK rho hsw p m d hdelta
      pi C hC muM hsqPi hT muL muU XiM sigmaM := by
  intro hin H hHK
  refine ⟨orbitSectionFixedCoefficients (decomposition p) d.compact pi H,
    finiteDimensional_orbitSectionFixedCoefficients (decomposition p) d.compact pi d.isCompact
      (compactOpenCofinal p d) H hHK, fun f hf => ?_⟩
  let Fourier := rationalSemistandardFourierOrbit hG hi hnu hKc hPK rho hsw
    p m d hdelta pi C hC muM hsqPi hT
  have hq : Fourier f ∈ SectionLevel H := by
    refine ⟨rationalSemistandardFourierSmoothness hG hi hnu hKc hPK rho hsw
      p m d hdelta pi C hC muM hsqPi hT muL muU XiM sigmaM hin f, fun x => ?_⟩
    have hx : Space.translate (rationalTranslationWeights K.isOpen hKc hPK rho)
        x.val.1 x.val.2 f = f :=
      Space.ext fun g => congrFun (hf.translate_eq x.property.1 x.property.2) g
    exact (rationalSemistandardFourierOrbit_translate hG hi hnu hKc hPK rho hsw
      p m d hdelta pi C hC muM hsqPi hT x.val.1 x.val.2 f).symm.trans (congrArg Fourier hx)
  refine ⟨hq, fun H' hH' => ?_, fun z => ?_⟩
  · exact orbitSectionLevelSubmodule_antitone m.normCharacters pi m.unitaryCoordinates.toMulEquiv
      (decomposition p) (isClosed_radical p) d.compact (isClosed_parabolic p) d.isCompact
      m.continuous_normCharacters d.projection_continuous d.factorization hH' hq
  · exact (orbitSectionLevelFixedRestriction (decomposition p) d.compact pi
      m.normCharacters m.unitaryCoordinates.toMulEquiv (isClosed_radical p) (isClosed_parabolic p)
      d.isCompact m.continuous_normCharacters d.projection_continuous d.factorization
      H hHK ⟨Fourier f, hq⟩ z).property

end Component

section FullProduct

variable {T : SemistandardSpectralIndex i → CommGroupScheme (Spec (CommRingCat.of F))}
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
    HasTemperedCoefficients (rationalXi hKc hPK) (rationalHeight (F := F) rho)
      ((normalizedInductionFunctor (decomposition p) (isClosed_radical p)).obj A.obj).representation)

set_option maxHeartbeats 2000000 in
/-- The component-level theorem applies to the published dependent product. -/
theorem rationalSemistandardFourierFamilySmoothness :
    RationalSemistandardFourierFamilySmoothnessStatement hG hi hnu hKc hPK rho hsw
      a ha muM d hdelta hT := by
  intro t muL muU XiM sigmaM hin f
  let p := t.1
  let m := chosenLeviModel p
  let pi := orbitRepresentative m (a p) (ha p) (muM p) t.2
  let C := m.splitCenter (a p)
  let hC := m.splitCenter_le_center (a p) (ha p)
  have hsqPi := orbitRepresentative_isSquareIntegrable m (a p) (ha p) (muM p) t.2
  exact rationalSemistandardFourierSmoothness hG hi hnu hKc hPK rho hsw
    p m (d p) (hdelta p) pi C hC (muM p) hsqPi
    (fun A => hT p A.val
      (unitaryOrbitRepresentative_isDiscreteSeries m.normCharacters pi C hC (muM p) hsqPi A))
    muL muU XiM sigmaM hin f

end FullProduct

end Langlands.HarishChandraSchwartz

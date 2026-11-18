import Langlands.HarmonicAnalysis.HarishChandraSchwartz.CuspidalWavePacketOrthogonality
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCuspidalSemistandardComparison
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardFourierFamily

/-! # The constant-term-to-Fourier implication in Waldspurger VIII.2.1 -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz

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

local instance cuspidalFourierCompactOpen : Nonempty (CompactOpenSubgroup (rationalPoints G)) :=
  ⟨Langlands.BruhatTits.rationalPointCompactOpenSubgroup F G⟩

local instance cuspidalFourierParabolicLC (p : SemistandardSpectralIndex i) :
    LocallyCompactSpace (parabolic p) :=
  (isClosed_parabolic p).locallyCompactSpace

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

/-- The actual proper Fourier component vanishes under the normalized
constant-term condition and the preceding hypotheses of VII.1.2. -/
theorem rationalSemistandardFourierFamily_apply_eq_zero_of_constantTermsVanish
    (t : RationalSemistandardTheta.{u, uV} a ha muM) (hproper : t.1.parabolic ≠ ⊤)
    (muL : Measure (levi t.1)) (muU : Measure (radical t.1)) (XiM sigmaM : levi t.1 → ℝ)
    (hUhaar : muU.IsHaarMeasure)
    (hin : RationalSemistandardFourierAnalyticInputs (muG := muG) hKc hPK rho
      t.1 (chosenLeviModel t.1) (d t.1)
      (orbitRepresentative (chosenLeviModel t.1) (a t.1) (ha t.1) (muM t.1) t.2)
      muL muU XiM sigmaM)
    (f : RationalSchwartzSpace hKc hPK rho)
    (hf : RationalSemistandardConstantTermsVanish (i := i) f) :
    rationalSemistandardFourierFamily hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT f t = 0 := by
  let := hin.ambient_inv
  let := hin.ambient_sigmaFinite
  let := hin.levi_left
  let := hin.levi_right
  let := hin.levi_inv
  let := hin.levi_sfinite
  let := hin.radical_left
  let := hin.radical_right
  let := hin.radical_sfinite
  let : Nonempty (CompactOpenSubgroup (levi t.1)) := by
    obtain ⟨L, hLc, _⟩ := compactOpenCofinal t.1 (d t.1) ⊤
    exact ⟨⟨L, hLc⟩⟩
  funext A
  rw [rationalSemistandardFourierFamily_apply,
    rationalSemistandardInducedFourierTransform_eq_inducedFourierTransform]
  refine inducedFourierTransform_eq_zero_of_constantTermInd_eq_zero
    (decomposition t.1) (isClosed_radical t.1) (isClosed_parabolic t.1)
    (d t.1).projection_continuous (d t.1).compact (d t.1).isCompact (d t.1).factorization_mem
    _ (hdelta t.1) A.val.obj (compactOpenCofinal t.1 (d t.1))
    ((chosenLeviModel t.1).splitCenter (a t.1))
    ((chosenLeviModel t.1).splitCenter_le_center (a t.1) (ha t.1)) (muM t.1) _ A.val.property.1
    (rationalL2Weights K.isOpen hKc hPK rho hsw) _ (rationalXi_inv hG hi hnu K.isOpen hKc hPK)
    (rationalHeight_inv rho) hin.radical_unimodular hin.levi_weights (hin.orbit_tempered A)
    hin.levi_xi_inv hin.levi_height_inv hin.constant_term hin.conjugation_modulus
    hin.constant_term_estimate (rationalTranslationWeights K.isOpen hKc hPK rho) hin.levi_translations
    hin.ambient_compact_volume hin.compact_factorization hin.levi_compact_volume
    hin.radical_compact_volume f (hin.double_integrability f A) ?_
  intro g
  apply Subtype.ext
  exact hf t.1 hproper muU hUhaar g

/-- The forward detection implication in VIII.2.1 for the actual intrinsic
kernel. The existing comparison to the full semistandard constant terms and
the preceding analytic inputs remain explicit. -/
def RationalSemistandardCuspidalProperFourierVanishingStatement : Prop :=
  RationalCuspidalSemistandardComparisonStatement.{u} → IsClosedSubgroup rho →
    (∀ (t : RationalSemistandardTheta.{u, uV} a ha muM), t.1.parabolic ≠ ⊤ →
      ∃ (muL : Measure (levi t.1)) (muU : Measure (radical t.1)) (XiM sigmaM : levi t.1 → ℝ),
        muU.IsHaarMeasure ∧
          RationalSemistandardFourierAnalyticInputs (muG := muG) hKc hPK rho
            t.1 (chosenLeviModel t.1) (d t.1)
            (orbitRepresentative (chosenLeviModel t.1) (a t.1) (ha t.1) (muM t.1) t.2)
            muL muU XiM sigmaM) →
    ∀ f : RationalSchwartzSpace hKc hPK rho, f ∈ rationalCuspidalSubmodule hKc hPK rho →
      ∀ (t : RationalSemistandardTheta.{u, uV} a ha muM), t.1.parabolic ≠ ⊤ →
        rationalSemistandardFourierFamily hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT f t = 0

theorem rationalSemistandardCuspidalProperFourierVanishing :
    RationalSemistandardCuspidalProperFourierVanishingStatement hG hi hnu hKc hPK rho hsw
      a ha muM d hdelta hT := by
  intro hcmp hrho hin f hf t ht
  obtain ⟨muL, muU, XiM, sigmaM, hUhaar, hinputs⟩ := hin t ht
  exact rationalSemistandardFourierFamily_apply_eq_zero_of_constantTermsVanish
    hG hi hnu hKc hPK rho hsw a ha muM d hdelta hT t ht muL muU XiM sigmaM hUhaar hinputs f
    ((hcmp F G hG S i hi nu hnu K hKc hPK N rho hrho f).mp hf)

end Langlands.HarishChandraSchwartz

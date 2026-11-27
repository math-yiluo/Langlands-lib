import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardWavePacketDetection

/-! # Positive definiteness of the source spectral form -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 1500000

universe u uV

open AlgebraicGeometry CategoryTheory MeasureTheory
open scoped CategoryTheory.MonObj ComplexConjugate
open Langlands.Aubert.General Langlands.GroupScheme Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz.RationalSemistandard.GlobalForm

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G}
  (hG : IsConnectedReductive G)
  {T : SemistandardSpectralIndex i → CommGroupScheme (Spec (CommRingCat.of F))}
  [∀ p, IsAffine (T p).X.left]
  (a : ∀ p, (T p).toGrp ⟶ (chosenLeviModel p).scheme)
  (ha : ∀ p, IsSplitComponent (a p))
  [∀ p, ((chosenLeviModel p).splitCenter (a p)).Normal]
  [∀ p, (rationalPoints.map (a p)).range.Normal]
  [∀ p, MeasurableSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))]
  [∀ p, BorelSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))]
  (mu : ∀ p, Measure (levi p ⧸ (chosenLeviModel p).splitCenter (a p)))
  [∀ p, (mu p).IsHaarMeasure] [∀ p, (mu p).IsInvInvariant]
  (d : ∀ p : SemistandardSpectralIndex i, CompactData p)
  (rs : ∀ p : SemistandardSpectralIndex i, CocharacterPresentation hG p)
  (hindex : ∀ p, (RenardCartan.splitValuationImage (a p)).FiniteIndex)
  (Q : ∀ θ : RationalSemistandardTheta.{u, uV} a ha mu,
    OrbitPacketData (rs θ.1)
      (orbitRepresentative (chosenLeviModel θ.1) (a θ.1) (ha θ.1) (mu θ.1) θ.2))

set_option hygiene false in
local notation "Theta" => RationalSemistandardTheta.{u, uV} a ha mu
set_option hygiene false in
local notation "Form" => componentForm hG a ha mu d rs hindex Q
set_option hygiene false in
local notation "Density" => componentDensity hG a ha mu rs Q
set_option hygiene false in
local notation "Sections" => rationalSemistandardThetaComponentSpace.{u, uV} a ha mu d

section Component

variable (θ : Theta)

set_option hygiene false in
local notation "p" => θ.1
set_option hygiene false in
local notation "m" => chosenLeviModel p
set_option hygiene false in
local notation "Z" => (m).splitCenter (a p)
set_option hygiene false in
local notation "hZ" => (m).splitCenter_le_center (a p) (ha p)
set_option hygiene false in
local notation "π" => orbitRepresentative m (a p) (ha p) (mu p) θ.2
set_option hygiene false in
local notation "hsq" => orbitRepresentative_isSquareIntegrable m (a p) (ha p) (mu p) θ.2
set_option hygiene false in
local notation "eta" => SourceMeasure.normalizedOrbitMeasure m (a p) (ha p) (hindex p) (mu p)
  (discreteSeriesClass Z hZ (mu p) π hsq)
set_option hygiene false in
local notation "pair" => SourceForm.pairing hG m (rs p) (d p) π Z hZ (mu p) hsq

variable (v w : smoothOrbitSections m (d p) π)

private theorem componentForm_conj
    (hn : DensityNonnegative hG a ha mu rs Q) :
    (starRingEnd ℂ) (Form θ w v) = Form θ v w := by
  change conj (∫ x, Density θ x * pair w v x ∂eta) =
    ∫ x, Density θ x * pair v w x ∂eta
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards with x
  change (starRingEnd ℂ) (Density θ x * pair w v x) = Density θ x * pair v w x
  have hp := SourceForm.pairing_conj_symm hG m (rs p) (d p) π Z hZ (mu p) hsq v w x
  rw [map_mul, hp]
  obtain ⟨b, _, hb⟩ := hn θ x
  simp [hb]

private theorem componentForm_self_nonneg
    (hn : DensityNonnegative hG a ha mu rs Q) :
    0 ≤ (Form θ v v).re := by
  change 0 ≤ (∫ x, Density θ x * pair v v x ∂eta).re
  have hinter := SourceForm.integrable_pairing hG m (rs p) (d p) (a p) (ha p) (hindex p)
    (mu p) π hsq (Q θ) v v
  have hre := integral_re hinter
  change (∫ x, (Density θ x * pair v v x).re ∂eta) =
    (∫ x, Density θ x * pair v v x ∂eta).re at hre
  rw [← hre]
  apply integral_nonneg
  intro x
  obtain ⟨b, hb, he⟩ := hn θ x
  change 0 ≤ (Density θ x * pair v v x).re
  rw [he, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  refine mul_nonneg hb ?_
  obtain ⟨A, rfl⟩ := unitaryOrbitRepresentativeDiscreteSeriesOrbit_surjective
    (m).normCharacters π Z hZ (mu p) hsq x
  rw [SourceForm.pairing_representative]
  exact (SourceForm.representativeForm hG m (rs p) (d p) π Z hZ (mu p) hsq A).re_inner_nonneg
    (v.val A)

end Component

variable (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))

set_option hygiene false in
local notation "familyForm" => rawGlobalForm hG a ha mu d rs hindex Q K hK
set_option hygiene false in
local notation "component" => rationalSemistandardThetaComponent a ha mu d
set_option hygiene false in
local notation "weight" => GlobalSynthesis.sourceWeight hG rs K hK

/-- The orbit forms and the positive source coefficients make the actual
finite spectral sum Hermitian and positive definite. -/
theorem positiveForm : PositiveFormStatement hG a ha mu d rs hindex Q K hK := by
  intro hfin hi hn hdense
  have hconj (f g : rationalSemistandardThetaSmoothSections.{u, uV} a ha mu d) :
      (starRingEnd ℂ) (familyForm g f) = familyForm f g := by
    have hf : (Function.support fun θ : Theta =>
        (weight θ.1 : ℂ) * Form θ (component θ g) (component θ f)).Finite := by
      apply (FiniteSupportSections.linearSummand_finite Sections
        (fun θ => ((weight θ.1 : ℂ) • Form θ) (component θ g)) f)
    rw [rawGlobalForm_finsum, rawGlobalForm_finsum, map_finsum (starRingEnd ℂ) hf]
    apply finsum_congr
    intro θ
    have hv := componentForm_conj hG a ha mu d rs hindex Q θ (component θ f) (component θ g) hn
    rw [map_mul, hv]
    simp
  have hterm (θ : Theta) (v : Sections θ) : 0 ≤ weight θ.1 * (Form θ v v).re :=
    mul_nonneg (SourceConstants.unquotientedWeight_pos (rs θ.1) K hK hi hfin).le
      (componentForm_self_nonneg hG a ha mu d rs hindex Q θ v hn)
  have hsum (f : rationalSemistandardThetaSmoothSections.{u, uV} a ha mu d) :
      (familyForm f f).re =
        ∑ θ ∈ f.property.2.toFinset, weight θ.1 * (Form θ (component θ f) (component θ f)).re := by
    rw [rawGlobalForm_apply]
    rw [Complex.re_sum]
    exact Finset.sum_congr rfl fun θ _ => by
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  refine ⟨hconj, fun f => (hsum f).symm ▸ Finset.sum_nonneg (fun θ _ => hterm θ (component θ f)), ?_⟩
  intro f hf
  have hfRe : (familyForm f f).re = 0 := congrArg Complex.re hf
  rw [hsum f] at hfRe
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun θ _ => hterm θ (component θ f))).mp hfRe
  apply rationalSemistandardThetaSmoothSections_ext a ha mu d
  intro θ
  rw [map_zero]
  by_cases hθ : θ ∈ f.property.2.toFinset
  · have hw := (SourceConstants.unquotientedWeight_pos (rs θ.1) K hK hi hfin).ne'
    have hre := (mul_eq_zero.mp (hz θ hθ)).resolve_left hw
    have hself := componentForm_conj hG a ha mu d rs hindex Q θ (component θ f) (component θ f) hn
    have him := congrArg Complex.im hself
    change (conj (Form θ (component θ f) (component θ f))).im =
      (Form θ (component θ f) (component θ f)).im at him
    rw [Complex.conj_im] at him
    have hzero : Form θ (component θ f) (component θ f) = 0 :=
      Complex.ext hre (by simpa only [Complex.zero_im] using neg_eq_self.mp him)
    exact (WavePacketPairing.componentForm_self_eq_zero_iff hG a ha mu d rs hindex Q θ hn
      hdense (component θ f)).mp hzero
  · apply Subtype.ext
    change f.val θ = 0
    exact by simpa only [Set.Finite.mem_toFinset, FiniteSupportSections.mem_support, not_not]
      using hθ

end Langlands.HarishChandraSchwartz.RationalSemistandard.GlobalForm

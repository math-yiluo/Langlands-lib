import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardAssociationSums
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardAssociationCount
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardInvariantForm
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardOrbitIntegralTransport
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardWeylWeight

/-! # The association formulas for the actual invariant source integrals -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 900000

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz.RationalSemistandard.Association

open GlobalSynthesis InvariantComparison WeylOrbits

attribute [local instance]
  rationalWeightsIsAffine rationalWeightsTopology rationalWeightsTopologicalGroup
  rationalWeightsT2Field rationalWeightsLocallyCompact rationalWeightsMeasurableSpace
  rationalWeightsBorelSpace rationalInducedSecondCountable rationalInducedT2
  rationalInducedNonarchimedean SourceMeasure.modelAffineHom SourceMeasure.modelAffine
  SourceMeasure.modelTopology

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G}
  {Z : SemistandardSpectralIndex i → CommGroupScheme (Spec (CommRingCat.of F))}
  {a : ∀ p, (Z p).toGrp ⟶ (chosenLeviModel p).scheme}
  {ha : ∀ p, IsSplitComponent (a p)}
  [∀ p, ((chosenLeviModel p).splitCenter (a p)).Normal]
  [∀ p, MeasurableSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))]
  [∀ p, BorelSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))]
  {mu : ∀ p, Measure (levi p ⧸ (chosenLeviModel p).splitCenter (a p))}
  [∀ p, (mu p).IsHaarMeasure]
  {d : ∀ p : SemistandardSpectralIndex i, CompactData p}
  {hG : IsConnectedReductive G}
  (C : WeylSectionComparisonData.{u, uV} a ha mu d hG)

set_option hygiene false in
set_option quotPrecheck false in
local notation "Θ" => RationalSemistandardTheta.{u, uV} a ha mu
set_option hygiene false in
local notation "Invariant" => rationalSemistandardThetaInvariantSections C
set_option hygiene false in
local notation "component" => rationalSemistandardThetaComponent a ha mu d

/-- Every associated target can be reached by a normalized comparison arrow
in the actual common source compact. -/
theorem exists_comparison_to_associated {t t' : Θ} (h : Associated a ha mu t t') :
    ∃ n : C.Lift t t'.1, C.target t t'.1 n = t' := by
  obtain ⟨w, hw⟩ := h
  obtain ⟨n, hn⟩ := C.exists_lift t t'.1 w (hw.levi_eq (C.centralizer_le t.1))
  have ht : WeylTransports a ha mu w t (C.target t t'.1 n) :=
    hn ▸ C.target_transports t t'.1 n
  exact ⟨n, ht.eq_of_same_parabolic hw (C.centralizer_le t.1) rfl⟩

/-- The invariant-family condition gives equality of the actual target
component with the smooth comparison, at the target's chosen base. -/
theorem component_eq_comparison (t : Θ) (q : SemistandardSpectralIndex i)
    (n : C.Lift t q) (f : Invariant) :
    component (C.target t q n) f.val = C.smoothComparison t q n (component t f.val) := by
  let T := C.smoothComparison t q n
  have h : T.symm (component (C.target t q n) f.val) = component t f.val := by
    apply Subtype.ext
    funext A
    let E := C.fiberComparisonEquiv t q n A
    have hv := congrArg (fun v => E.symm v) (f.property t q n A)
    exact (C.smoothComparison_symm_apply t q n (component (C.target t q n) f.val) A).trans
      (hv.trans (E.symm_apply_apply (f.val.val t A)))
  exact (T.apply_symm_apply _).symm.trans (congrArg T h)

variable (K0 : OpenSubgroup (rationalPoints G)) (hK0 : IsCompact (K0 : Set (rationalPoints G)))

set_option hygiene false in
local notation "weight" => sourceWeight hG C.presentation K0 hK0

/-- Waldspurger's coefficient of an actual association representative. -/
def coefficientAtRepresentative (t : Θ) : ℝ :=
  associationWeight hG a ha mu t (C.centralizer_le t.1) (C.presentation t.1) K0 hK0

section Regrouping

variable (hi : IsMaximalSplitTorus i)
  (hD : SemistandardSpectralDynamicCoverageStatement.{u})
  (hfin : SemistandardSpectralFiberFinitenessStatement.{u})
  (hI : SourceConstantParabolicIndependenceStatement (i := i) hG)
  (nu : cocharacterLattice S) (hnu : IsGenericCocharacter i nu)
  (hspecial : SpecialCompactProperties F i nu (K0 : Subgroup (rationalPoints G)))

include hi hD hI hnu hspecial in
omit [∀ p, BorelSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))] in
/-- The unquotiented source coefficient is constant on actual association classes. -/
theorem sourceWeight_eq_of_associated {t t' : Θ} (h : Associated a ha mu t t') :
    weight t.1 = weight t'.1 := by
  obtain ⟨w, hw⟩ := h
  let hp := C.centralizer_le t.1
  have h' := SourceConstants.unquotientedWeightAtIndex_eq_at_weylConjugateLevi hG hi hD hI
    nu hnu K0 hK0 hspecial t.1 t'.1 hp w (hw.levi_eq hp).symm
  exact (SourceConstants.unquotientedWeightAtIndex_eq hi K0 hK0 hD (C.presentation t.1)).symm.trans
    (h'.symm.trans (SourceConstants.unquotientedWeightAtIndex_eq hi K0 hK0 hD (C.presentation t'.1)))

omit [∀ p, BorelSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))] in
private theorem weighted_support_subset (f : Θ → ℂ) :
    Function.support (fun t => (weight t.1 : ℂ) * f t) ⊆ Function.support f := by
  intro t ht hzero
  exact ht (by simp only [hzero, mul_zero])

include hi hD hfin hI hnu hspecial in
private theorem associationRegroup (R : Representatives.{u, uV} a ha mu)
    (f : Θ → ℂ) (hf : (Function.support f).Finite)
    (hc : ∀ t t', Associated a ha mu t t' → f t = f t') :
    (∑ᶠ t, (weight t.1 : ℂ) * f t) =
      representativeSum a ha mu R (fun t => (coefficientAtRepresentative C K0 hK0 t : ℂ) * f t) := by
  have hconst (t t' : Θ) (h : Associated a ha mu t t') :
      (weight t.1 : ℂ) * f t = (weight t'.1 : ℂ) * f t' := by
    rw [sourceWeight_eq_of_associated C K0 hK0 hi hD hI nu hnu hspecial h, hc t t' h]
  refine (finsum_eq_representativeSum a ha mu R hG hi
    (semistandardLeviCentralizerContainment_of_dynamicCoverage hD) hfin
    (fun t => (weight t.1 : ℂ) * f t) (hf.subset (weighted_support_subset C K0 hK0 f))
    hconst).trans ?_
  unfold representativeSum
  apply finsum_congr
  intro c
  let t := R.select c
  have hw := card_association_mul_unquotientedWeight hG hi hD a ha mu t
    (C.centralizer_le t.1) (C.presentation t.1) K0 hK0 hfin
  change (Nat.card (associatedIndices a ha mu t)) • ((weight t.1 : ℂ) * f t) =
    (coefficientAtRepresentative C K0 hK0 t : ℂ) * f t
  rw [nsmul_eq_mul, ← mul_assoc, ← Complex.ofReal_natCast, ← Complex.ofReal_mul]
  exact congrArg (fun x : ℝ => (x : ℂ) * f t) hw

end Regrouping

variable [∀ p, IsAffine (Z p).X.left] [∀ p, (rationalPoints.map (a p)).range.Normal]
  (hindex : ∀ p, (RenardCartan.splitValuationImage (a p)).FiniteIndex)
  (Q : ∀ t : Θ, OrbitPacketData (C.presentation t.1) (base a ha mu t))

set_option hygiene false in
local notation "packet" => componentPacket hG a ha mu d C.presentation hindex Q

private def packetValue (f : Invariant) (g : rationalPoints G) (t : Θ) : ℂ :=
  packet t (component t f.val) g

private theorem packetValue_support (f : Invariant) (g : rationalPoints G) :
    Function.support (packetValue C hindex Q f g) ⊆ FiniteSupportSections.support f.val.val := by
  intro t ht hzero
  have h : component t f.val = 0 := Subtype.ext hzero
  exact ht (by simp only [packetValue, h, map_zero, Pi.zero_apply])

/-- The synthesis sum over arbitrary actual association representatives. -/
def packetRepresentativeSum (R : Representatives.{u, uV} a ha mu)
    (f : Invariant) (g : rationalPoints G) : ℂ :=
  representativeSum a ha mu R (fun t =>
    (coefficientAtRepresentative C K0 hK0 t : ℂ) * packetValue C hindex Q f g t)

theorem packetRepresentativeSum_eq_finiteSum (R : Representatives.{u, uV} a ha mu)
    (f : Invariant) (g : rationalPoints G) :
    packetRepresentativeSum C K0 hK0 hindex Q R f g =
      ∑ c ∈ (f.val.property.2.image (classOf a ha mu)).toFinset,
        (coefficientAtRepresentative C K0 hK0 (R.select c) : ℂ) *
          packet (R.select c) (component (R.select c) f.val) g := by
  apply representativeSum_eq_sum a ha mu R _ f.val.property.2
  intro t ht
  exact packetValue_support C hindex Q f g (fun h => ht (by simp only [h, mul_zero]))

section Form

variable [∀ p, (mu p).IsInvInvariant]

set_option hygiene false in
local notation "form" => GlobalForm.componentForm hG a ha mu d C.presentation hindex Q

private def formValue (f' f : Invariant) (t : Θ) : ℂ :=
  form t (component t f'.val) (component t f.val)

private theorem formValue_support (f' f : Invariant) :
    Function.support (formValue C hindex Q f' f) ⊆ FiniteSupportSections.support f.val.val := by
  intro t ht hzero
  have h : component t f.val = 0 := Subtype.ext hzero
  exact ht (by simp only [formValue, h, map_zero])

/-- The global form sum over arbitrary actual association representatives. -/
def formRepresentativeSum (R : Representatives.{u, uV} a ha mu) (f' f : Invariant) : ℂ :=
  representativeSum a ha mu R (fun t =>
    (coefficientAtRepresentative C K0 hK0 t : ℂ) * formValue C hindex Q f' f t)

theorem formRepresentativeSum_eq_finiteSum (R : Representatives.{u, uV} a ha mu)
    (f' f : Invariant) :
    formRepresentativeSum C K0 hK0 hindex Q R f' f =
      ∑ c ∈ (f.val.property.2.image (classOf a ha mu)).toFinset,
        (coefficientAtRepresentative C K0 hK0 (R.select c) : ℂ) *
          form (R.select c) (component (R.select c) f'.val) (component (R.select c) f.val) := by
  apply representativeSum_eq_sum a ha mu R _ f.val.property.2
  intro t ht
  exact formValue_support C hindex Q f' f (fun h => ht (by simp only [h, mul_zero]))

set_option hygiene false in
local notation "synthesis" => weightedSynthesis hG a ha mu d C.presentation hindex Q K0 hK0
set_option hygiene false in
local notation "formInvariant" => GlobalForm.invariantGlobalForm hG a ha mu d C.presentation
  hindex Q K0 hK0 C

/-- Remark VII.2.4 for the actual invariant source synthesis and form. -/
def AssociationFormulaStatement : Prop :=
  ∀ R : Representatives.{u, uV} a ha mu,
    (∀ (f : Invariant) (g : rationalPoints G),
      synthesis f.val g = packetRepresentativeSum C K0 hK0 hindex Q R f g) ∧
    (∀ f' f : Invariant,
      formInvariant f' f = formRepresentativeSum C K0 hK0 hindex Q R f' f)

variable (hi : IsMaximalSplitTorus i)
  (hD : SemistandardSpectralDynamicCoverageStatement.{u})
  (hfin : SemistandardSpectralFiberFinitenessStatement.{u})
  (hI : SourceConstantParabolicIndependenceStatement (i := i) hG)
  (nu : cocharacterLattice S) (hnu : IsGenericCocharacter i nu)
  (hspecial : SpecialCompactProperties F i nu (K0 : Subgroup (rationalPoints G)))
  (hd : ∀ p, (d p).compact = K0) (hQ : ∀ t : Θ, (Q t).compact = K0)
  (hE : C.CoefficientTransportStatement) (hDensity : C.DensityTransportStatement Q)
  (hn : SourceMeasure.IntrinsicQuotientNormalization a mu d)
  (hForm : C.PairingTransportStatement)

include hi hD hfin hI hnu hspecial hd hQ hE hDensity hn hForm in
/-- Regroup the actual integrals using the preceding one-orbit transport,
common-Levi source constants and geometric multiplicity. -/
theorem associationFormula_of_transport :
    AssociationFormulaStatement C K0 hK0 hindex Q := by
  have hcompact (t : Θ) : (Q t).compact = (d t.1).compact := (hQ t).trans (hd t.1).symm
  intro R
  constructor
  · intro f g
    let f₀ := packetValue C hindex Q f g
    have hc (t t' : Θ) (h : Associated a ha mu t t') : f₀ t = f₀ t' := by
      obtain ⟨n, htarget⟩ := exists_comparison_to_associated C h
      let q := t'.1
      have he := component_eq_comparison C t q n f
      have hp := C.componentPacket_transport t q n Q hindex hE hDensity hcompact (component t f.val)
      have hh := congrArg (fun v => packet (C.target t q n) v g) he
      exact (congrFun hp g).symm.trans (hh.symm.trans (congrArg f₀ htarget))
    have hsupport := packetValue_support C hindex Q f g
    have hsum := finsum_eq_sum_of_support_subset _ (fun t ht => f.val.property.2.mem_toFinset.mpr
      (hsupport (weighted_support_subset C K0 hK0 f₀ ht)))
    exact (weightedSynthesis_apply hG a ha mu d C.presentation hindex Q K0 hK0 f.val g).trans
      (hsum.symm.trans (associationRegroup C K0 hK0 hi hD hfin hI nu hnu hspecial R f₀
        (f.val.property.2.subset hsupport) hc))
  · intro f' f
    let f₀ := formValue C hindex Q f' f
    have hc (t t' : Θ) (h : Associated a ha mu t t') : f₀ t = f₀ t' := by
      obtain ⟨n, htarget⟩ := exists_comparison_to_associated C h
      let q := t'.1
      have he' := component_eq_comparison C t q n f'
      have he := component_eq_comparison C t q n f
      have hi' := C.componentForm_transport t q n Q hindex hForm hn hDensity hcompact
        (component t f'.val) (component t f.val)
      have hh := congrArg₂ (fun u v => form (C.target t q n) u v) he' he
      exact hi'.symm.trans (hh.symm.trans (congrArg f₀ htarget))
    exact (GlobalForm.rawGlobalForm_finsum hG a ha mu d C.presentation hindex Q K0 hK0
      f'.val f.val).trans (associationRegroup C K0 hK0 hi hD hfin hI nu hnu hspecial R f₀
        (f.val.property.2.subset (formValue_support C hindex Q f' f)) hc)

/-- The reduced synthesis is independent of the association representatives. -/
theorem packetRepresentativeSum_independent (h : AssociationFormulaStatement C K0 hK0 hindex Q)
    (R R' : Representatives.{u, uV} a ha mu) (f : Invariant) (g : rationalPoints G) :
    packetRepresentativeSum C K0 hK0 hindex Q R f g =
      packetRepresentativeSum C K0 hK0 hindex Q R' f g :=
  ((h R).1 f g).symm.trans ((h R').1 f g)

/-- The reduced global form is independent of the association representatives. -/
theorem formRepresentativeSum_independent (h : AssociationFormulaStatement C K0 hK0 hindex Q)
    (R R' : Representatives.{u, uV} a ha mu) (f' f : Invariant) :
    formRepresentativeSum C K0 hK0 hindex Q R f' f =
      formRepresentativeSum C K0 hK0 hindex Q R' f' f :=
  ((h R).2 f' f).symm.trans ((h R').2 f' f)

end Form

end Langlands.HarishChandraSchwartz.RationalSemistandard.Association

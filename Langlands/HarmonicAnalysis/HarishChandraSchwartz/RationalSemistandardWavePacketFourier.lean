import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardFourierFamily
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardWavePacketPairing
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardWavePacketTransport
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardWeylDescentStatement
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWavePacketCentralNormalization

/-! # The Fourier Weyl sum for an actual semistandard wave packet -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj BigOperators
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel Langlands.Induction
open Langlands.BruhatTits.SpecialCompact (HasWeylRepresentatives SpecialCompactProperties)

namespace Langlands.HarishChandraSchwartz.RationalSemistandard.WavePacketPairing

open Association WeylOrbits WeylSections WeylDescent WeylComparison
open ActualConjugateLeviCoherence (LeviNormalization)
open WaldspurgerSourceNormalization
  (IsSourceCompactAt IsNormalizedQuotientHaar normalizedQuotientHaar_map_iff)

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean
  DynamicOppositeStandardIntertwining.centralizerClosedImmersion
  DynamicOppositeStandardIntertwining.centralizerAffine
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace2
  LeviNormalization.normal LeviNormalization.quotientMeasurable LeviNormalization.quotientBorel
  LeviNormalization.quotientHaar LeviNormalization.quotientInversion

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G}

local instance dynamicLeviLocallyCompact (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) :
    LocallyCompactSpace (DynamicOppositeStandardIntertwining.levi χ) :=
  (DynamicOppositeStandardIntertwining.levi_isClosed χ).locallyCompactSpace

section Lifts

variable {hG : IsConnectedReductive G} {p q : SemistandardSpectralIndex i}

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
/-- The required centralizer containment is supplied by the actual cocharacter presentation. -/
theorem sourceTorusCentralizer_le_levi (r : CocharacterPresentation hG p) :
    torusCentralizer i ≤ p.levi :=
  r.levi_eq ▸ torusCentralizer_le_dynamicCentralizer i (CommGroupScheme.groupHom r.cocharacter)

variable (d : CompactData p) (hP : torusCentralizer i ≤ p.levi)

set_option hygiene false in
local notation "WQ" => SemistandardWeylConjugacyQuotient i p.toLevi q.toLevi hP
set_option hygiene false in
local notation "Lift" => CompactLift (p := p) (q := q) hP d.compact

/-- Choose one actual lift in the fixed compact for each left target-Levi class. -/
def compactWeylLift (hw : HasWeylRepresentatives i d.compact.toSubgroup) (w : WQ) :
    {n : Lift // liftClass d hP n = w} :=
  ⟨Classical.choose (liftClass_surjective d hP hw w),
    Classical.choose_spec (liftClass_surjective d hP hw w)⟩

variable (n : Lift)

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
/-- The compact lift gives the actual all-test conjugation of the two Levis. -/
theorem compactLiftConjugatesLevi : ConjugatesLevi (n.val : rationalPoints G) p q := by
  change p.levi = q.levi.comap (G.innerIso (n.val : rationalPoints G)).hom
  rw [← conjugateLevi_eq hP d.compact n, ← SubgroupFunctor.comap_comp,
    Iso.hom_inv_id, SubgroupFunctor.comap_id]

/-- Both comparison interfaces pull back by the same inner conjugation on literal points. -/
theorem compactLift_leviPullback :
    leviPullback hP d.compact n = (leviPointConjugation (compactLiftConjugatesLevi d hP n)).symm := by
  ext x
  rfl

end Lifts

variable (hG : IsConnectedReductive G)
  {T : SemistandardSpectralIndex i → CommGroupScheme (Spec (CommRingCat.of F))}
  (a : ∀ p, (T p).toGrp ⟶ (chosenLeviModel p).scheme)
  (ha : ∀ p, IsSplitComponent (a p))
  [∀ p, ((chosenLeviModel p).splitCenter (a p)).Normal]
  [∀ p, MeasurableSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))]
  [∀ p, BorelSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))]
  (mu : ∀ p, Measure (levi p ⧸ (chosenLeviModel p).splitCenter (a p)))
  [∀ p, (mu p).IsHaarMeasure]
  (d : ∀ p : SemistandardSpectralIndex i, CompactData p)
  (rs : ∀ p : SemistandardSpectralIndex i, CocharacterPresentation hG p)

set_option hygiene false in
local notation "Theta" => RationalSemistandardTheta.{u, uV} a ha mu
set_option hygiene false in
local notation "Sections" => rationalSemistandardThetaComponentSpace.{u, uV} a ha mu d
set_option hygiene false in
local notation "Center" p:max => (chosenLeviModel p).splitCenter (a p)
set_option hygiene false in
local notation "Central" p:max => (chosenLeviModel p).splitCenter_le_center (a p) (ha p)
set_option hygiene false in
local notation "base" t:max =>
  orbitRepresentative (chosenLeviModel t.1) (a t.1) (ha t.1) (mu t.1) t.2
set_option hygiene false in
local notation "sqBase" t:max =>
  orbitRepresentative_isSquareIntegrable (chosenLeviModel t.1) (a t.1) (ha t.1) (mu t.1) t.2
set_option hygiene false in
local notation "omegaBase" t:max => discreteSeriesClass (Center t.1) (Central t.1) (mu t.1) (base t) (sqBase t)
set_option hygiene false in
local notation "Rep" t:max => UnitaryOrbitRepresentative (chosenLeviModel t.1).normCharacters (base t)
set_option hygiene false in
local notation "hCentralizer" p:max => sourceTorusCentralizer_le_levi (rs p)

section OrbitComparison

variable (t : Theta) {q : SemistandardSpectralIndex i}

set_option hygiene false in
local notation "WQ" => SemistandardWeylConjugacyQuotient i t.1.toLevi q.toLevi (hCentralizer t.1)
set_option hygiene false in
local notation "Lift" => CompactLift (q := q) (hCentralizer t.1) (d t.1).compact
set_option hygiene false in
local notation "hc" n:max => compactLiftConjugatesLevi (d t.1) (hCentralizer t.1) n
set_option hygiene false in
local notation "target" n:max => conjugateFullIndex a ha mu t q (hc n)
set_option hygiene false in
local notation "piConj" n:max => conjugateBase (hCentralizer t.1) (d t.1).compact n (base t)
set_option hygiene false in
local notation "AConj" n:max A:max => conjugateRepresentative (hCentralizer t.1) (d t.1).compact n
  (chosenLeviModel t.1) (chosenLeviModel q) (base t) A

variable (n : Lift)

/-- The Weyl comparison and orbit transport use the same inducing object at each representative. -/
theorem compactLift_conjugateRepresentative_val (A : Rep t) :
    (AConj n A).val = (conjugateOrbitRepresentative a ha mu t q (hc n) A).val := by
  change IrreducibleAdmissibleRep.pullback (leviPullback (hCentralizer t.1) (d t.1).compact n)
      A.val = IrreducibleAdmissibleRep.pullback (leviPointConjugation (hc n)).symm A.val
  rw [compactLift_leviPullback]

/-- The compact-lift comparison's base belongs to the actual conjugated discrete series. -/
theorem compactLift_base_squareIntegrable :
    IsSquareIntegrableModCentralSubgroup (Center q) (Central q) (piConj n).obj.representation (mu q) := by
  change IsSquareIntegrableModCentralSubgroup (Center q) (Central q)
    (IrreducibleAdmissibleRep.pullback (leviPullback (hCentralizer t.1) (d t.1).compact n)
      (base t)).obj.representation (mu q)
  rw [compactLift_leviPullback]
  exact (conjugateDiscreteSeriesClass (hc n) (chosenLeviModel t.1) (chosenLeviModel q)
    (a t.1) (ha t.1) (a q) (ha q) (mu t.1) (mu q) (omegaBase t)).property

set_option hygiene false in
local notation "sqConj" n:max => compactLift_base_squareIntegrable hG a ha mu d rs t n

/-- The comparison base has the orbit class computed by actual Levi conjugation. -/
theorem compactLift_base_orbit :
    (Quotient.mk _ (discreteSeriesClass (Center q) (Central q) (mu q) (piConj n) (sqConj n)) :
      OrbitClass (chosenLeviModel q) (a q) (ha q) (mu q)) = (target n).2 := by
  let push := conjugateOrbit (hc n) (chosenLeviModel t.1) (chosenLeviModel q)
    (a t.1) (ha t.1) (a q) (ha q) (mu t.1) (mu q)
  have he := congrArg push (mk_discreteSeriesClass_orbitRepresentative
    (chosenLeviModel t.1) (a t.1) (ha t.1) (mu t.1) t.2)
  have hclass : discreteSeriesClass (Center q) (Central q) (mu q) (piConj n) (sqConj n) =
      conjugateDiscreteSeriesClass (hc n) (chosenLeviModel t.1) (chosenLeviModel q)
        (a t.1) (ha t.1) (a q) (ha q) (mu t.1) (mu q) (omegaBase t) := by
    apply Subtype.ext
    change Quotient.mk _ (IrreducibleAdmissibleRep.pullback
      (leviPullback (hCentralizer t.1) (d t.1).compact n) (base t)) =
      Quotient.mk _ (IrreducibleAdmissibleRep.pullback (leviPointConjugation (hc n)).symm (base t))
    rw [compactLift_leviPullback]
  rw [hclass]
  exact he

/-- Retain every actual target inducing object when recentering the comparison. -/
def compactLiftTargetBaseEquiv
    (O : OrbitClass.{u, uV} (chosenLeviModel q) (a q) (ha q) (mu q))
    (hO : (target n).2 = O) :
    Sections (⟨q, O⟩ : Theta) ≃ₗ[ℂ] smoothOrbitSections (chosenLeviModel q) (d q) (piConj n) :=
  orbitSmoothSectionsBaseEquiv (chosenLeviModel q) (a q) (ha q) (mu q) (d q) O
    (piConj n) (sqConj n) ((compactLift_base_orbit hG a ha mu d rs t n).trans hO)

variable (t' : Theta)

/-- The quotient filter can be tested at any compact lift by actual orbit conjugation. -/
theorem compactLift_target_eq_iff (n : CompactLift (q := t'.1) (hCentralizer t.1) (d t.1).compact) :
    conjugateFullIndex a ha mu t t'.1 (hc n) = t' ↔
      quotientWeylTransports a ha mu t t' (hCentralizer t.1)
        (conjugacyQuotientToTransporter a ha mu t t' (hCentralizer t.1)
          (liftClass (d t.1) (hCentralizer t.1) n)) := by
  change conjugateFullIndex a ha mu t t'.1 (hc n) = t' ↔
    WeylTransports a ha mu (QuotientGroup.mk n.val) t t'
  constructor
  · intro h
    exact ⟨n.val, rfl, (congrArg (OrbitConjugates a ha mu (n.val : rationalPoints G) t) h).mp
      (orbitConjugates_conjugateFullIndex a ha mu t t'.1 (hc n))⟩
  · exact conjugateFullIndex_eq_of_weylTransports a ha mu t t' (hCentralizer t.1) n.val (hc n)

omit t' in
/-- The filter at a discrete-series class is Waldspurger's inverse constituent test. -/
theorem compactLift_transports_iff_inverse_constituent (n : Lift)
    (omega : DiscreteSeriesClass.{u, uV} (Center q) (Central q) (mu q)) :
    let t' : Theta := ⟨q, Quotient.mk _ omega⟩
    quotientWeylTransports a ha mu t t' (hCentralizer t.1)
      (conjugacyQuotientToTransporter a ha mu t t' (hCentralizer t.1)
        (liftClass (d t.1) (hCentralizer t.1) n)) ↔
      SmoothDualClass.pullback (leviPointConjugation (hc n)) omega.val ∈ orbitConstituents a ha mu t := by
  dsimp only
  refine (compactLift_target_eq_iff hG a ha mu d rs t ⟨q, Quotient.mk _ omega⟩ n).symm.trans ?_
  refine Iff.trans ?_ (mem_conjugateFullIndex_iff a ha mu t q (hc n) omega.val)
  constructor
  · intro ht
    exact (mem_orbitConstituents_iff a ha mu (target n) omega).mpr
      (eq_of_heq ((Sigma.ext_iff.mp ht).2)).symm
  · intro hm
    exact congrArg (Sigma.mk q) ((mem_orbitConstituents_iff a ha mu (target n) omega).mp hm).symm

end OrbitComparison

section SourceMeasure

variable {K : OpenSubgroup (rationalPoints G)}

/-- The I.1 quotient Haar gives the image of the literal compact Levi trace mass one. -/
def SourceLeviQuotientHaar (p : SemistandardSpectralIndex i) : Prop :=
  IsNormalizedQuotientHaar (Center p)
    (K.comap (levi p).subtype continuous_subtype_val) (mu p)

variable (t : Theta) (D : LeviNormalization (rs t.1).hom (dynamicInducing (rs t.1) (base t).obj))

/-- The dynamic comparison uses the same split-central quotient and measure as the source packet. -/
def LeviNormalizationMatches : Prop :=
  let e := (rs t.1).literalLeviHomeomorph
  ∃ hC : D.center.map e.toMonoidHom = Center t.1,
    D.quotientMeasure.map (quotientContinuousMulEquiv e (Center t.1) D.center hC) = mu t.1

/-- The source mass-one trace normalization passes to the dynamic comparison. -/
theorem hasIntrinsicSourceNormalization_of_match
    (hcompact : IsSourceCompactAt i (d t.1).compact.toSubgroup)
    (hmu : IsNormalizedQuotientHaar (Center t.1)
      ((d t.1).compact.comap (levi t.1).subtype continuous_subtype_val) (mu t.1))
    (hD : LeviNormalizationMatches hG a ha mu rs t D) :
    HasIntrinsicSourceNormalization (d t.1) (base t) (rs t.1) D := by
  obtain ⟨hC, he⟩ := hD
  refine ⟨hcompact, ?_⟩
  apply (normalizedQuotientHaar_map_iff (Center t.1)
    ((d t.1).compact.comap (levi t.1).subtype continuous_subtype_val)
    D.center _ (rs t.1).literalLeviHomeomorph hC (fun _ => Iff.rfl) D.quotientMeasure).mp
  rw [he]
  exact hmu

/-- Common compact compatibility supplies the trace and apartment normalization in the source model. -/
theorem hasIntrinsicSourceNormalization_of_commonCompact
    (hk : (d t.1).compact = K) (hcompact : IsSourceCompactAt i K.toSubgroup)
    (hmu : SourceLeviQuotientHaar a mu (K := K) t.1)
    (hD : LeviNormalizationMatches hG a ha mu rs t D) :
    HasIntrinsicSourceNormalization (d t.1) (base t) (rs t.1) D := by
  apply hasIntrinsicSourceNormalization_of_match hG a ha mu d rs t D _ _ hD
  · rw [hk]
    exact hcompact
  · rw [hk]
    exact hmu

end SourceMeasure

section Recenter

variable {q : SemistandardSpectralIndex i} (m : LeviModel q) (e : CompactData q)
  (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi q))

private theorem recenterSections_comp_apply
    (A B : UnitaryOrbitRepresentative m.normCharacters π) (v : smoothOrbitSections m e π) :
    recenterSections m e A.val (unitaryOrbitRepresentativeBaseEquiv m.normCharacters π A B)
        (recenterSections m e π A v) =
      recenterSections m e π B v := by
  apply Subtype.ext
  funext C
  rfl

end Recenter

section CertifiedComparison

variable (t t' : Theta)

set_option hygiene false in
local notation "WQ" => SemistandardWeylConjugacyQuotient i t.1.toLevi t'.1.toLevi (hCentralizer t.1)
set_option hygiene false in
local notation "OW" => OrbitWeylTransporters a ha mu t t' (hCentralizer t.1)
set_option hygiene false in
local notation "Lift" => CompactLift (q := t'.1) (hCentralizer t.1) (d t.1).compact
set_option hygiene false in
local notation "classOf" => liftClass (q := t'.1) (d t.1) (hCentralizer t.1)
set_option hygiene false in
local notation "target" n:max => conjugateFullIndex a ha mu t t'.1
  (compactLiftConjugatesLevi (d t.1) (hCentralizer t.1) n)
set_option hygiene false in
local notation "inTargetBase" n:max h:max =>
  compactLiftTargetBaseEquiv hG a ha mu d rs t n t'.2 h
set_option hygiene false in
local notation "piConj" n:max => conjugateBase (hCentralizer t.1) (d t.1).compact n (base t)
set_option hygiene false in
local notation "AConj" n:max A:max => conjugateRepresentative (hCentralizer t.1) (d t.1).compact n
  (chosenLeviModel t.1) (chosenLeviModel t'.1) (base t) A

/-- Every lift of a retained class transports the source to the specified target orbit. -/
theorem compactLift_targetOrbit (w : OW) (n : Lift) (hn : classOf n = w.val) :
    (target n).2 = t'.2 := by
  have ht := (compactLift_target_eq_iff hG a ha mu d rs t t' n).mpr
    (by rw [hn]; exact w.property)
  exact eq_of_heq ((Sigma.ext_iff.mp ht).2)

/-- The representative with the actual conjugate inducing object in the specified target orbit. -/
def compactLiftTargetRepresentative (n : Lift) (hO : (target n).2 = t'.2) (A : Rep t) : Rep t' :=
  let m' := chosenLeviModel t'.1
  let B := orbitRepresentativeMember m' (a t'.1) (ha t'.1) (mu t'.1) t'.2 (piConj n)
    (compactLift_base_squareIntegrable hG a ha mu d rs t n)
    ((compactLift_base_orbit hG a ha mu d rs t n).trans hO)
  (unitaryOrbitRepresentativeBaseEquiv m'.normCharacters (base t') B).symm (AConj n A)

/-- Reindexing a section to the comparison base evaluates it at the same actual inducing object. -/
theorem compactLiftTargetBaseEquiv_apply (n : Lift) (hO : (target n).2 = t'.2)
    (v : Sections t') (A : Rep t) :
    ((inTargetBase n hO) v).val (AConj n A) =
      v.val (compactLiftTargetRepresentative hG a ha mu d rs t t' n hO A) :=
  rfl

/-- Pull a specified target representative back to the actual source orbit. -/
def compactLiftSourceRepresentative (w : OW) (n : Lift) (hn : classOf n = w.val)
    (B : Rep t') : Rep t := by
  let hc := compactLiftConjugatesLevi (d t.1) (hCentralizer t.1) n
  let e := leviPointConjugation hc
  let omega := unitaryOrbitRepresentativeDiscreteSeriesOrbit
    (chosenLeviModel t'.1).normCharacters (base t') (Center t'.1) (Central t'.1)
    (mu t'.1) (sqBase t') B
  refine ⟨IrreducibleAdmissibleRep.pullback e B.val, ?_⟩
  have hO := compactLift_targetOrbit hG a ha mu d rs t t' w n hn
  have hm := (mem_orbitConstituents_iff a ha mu (target n) omega.val).mpr
    ((orbitPoint_mk a ha mu t' omega).trans hO.symm)
  obtain ⟨omega₀, he, hOrbit⟩ :=
    (mem_conjugateFullIndex_iff a ha mu t t'.1 hc omega.val.val).mp hm
  obtain ⟨χ, hχ⟩ := Quotient.exact (hOrbit.trans
    (mk_discreteSeriesClass_orbitRepresentative (chosenLeviModel t.1) (a t.1)
      (ha t.1) (mu t.1) t.2).symm)
  exact ⟨χ, (congrArg Subtype.val hχ).trans he⟩

/-- Cancellation of the two Levi conjugations gives the actual inducing equivalence. -/
def compactLiftInverseInducingEquiv (w : OW) (n : Lift) (hn : classOf n = w.val)
    (B : Rep t') :
    (AConj n (compactLiftSourceRepresentative hG a ha mu d rs t t' w n hn B)).val.obj.representation.Equiv
      B.val.obj.representation := by
  let e := leviPointConjugation (compactLiftConjugatesLevi (d t.1) (hCentralizer t.1) n)
  change (SmoothRep.pullback (leviPullback (hCentralizer t.1) (d t.1).compact n)
    (SmoothRep.pullback e B.val.obj)).representation.Equiv B.val.obj.representation
  rw [compactLift_leviPullback]
  exact SmoothRep.equivOfIso (SmoothRep.pullbackSymmIso e B.val.obj)

set_option maxHeartbeats 450000 in
/-- Recentring between lifts commutes with the intrinsic target-orbit base changes. -/
theorem recenterTarget_compactLiftTargetBaseEquiv
    (n n' : Lift) (h : classOf n = classOf n')
    (hO : (target n).2 = t'.2) (hO' : (target n').2 = t'.2) (v : Sections t') :
    recenterTarget (chosenLeviModel t'.1) (d t.1) (d t'.1) (hCentralizer t.1)
        (hCentralizer t'.1) (base t) n n' h ((inTargetBase n hO) v) =
      (inTargetBase n' hO') v := by
  let m := chosenLeviModel t'.1
  let e := d t'.1
  let A := orbitRepresentativeMember m (a t'.1) (ha t'.1) (mu t'.1) t'.2 (piConj n)
    (compactLift_base_squareIntegrable hG a ha mu d rs t n)
    ((compactLift_base_orbit hG a ha mu d rs t n).trans hO)
  let A' := orbitRepresentativeMember m (a t'.1) (ha t'.1) (mu t'.1) t'.2 (piConj n')
    (compactLift_base_squareIntegrable hG a ha mu d rs t n')
    ((compactLift_base_orbit hG a ha mu d rs t n').trans hO')
  let B := unitaryOrbitRepresentativeBaseEquiv m.normCharacters (base t') A A'
  change recenterSections m e A.val B (recenterSections m e (base t') A v) =
    recenterSections m e (base t') A' v
  exact recenterSections_comp_apply m e (base t') A A' v

variable (hk : (d t'.1).compact = (d t.1).compact)
  (D : LeviNormalization (rs t.1).hom (dynamicInducing (rs t.1) (base t).obj))

/-- The actual normalized-comparison descent specialized to the two full spectral indices. -/
abbrev OrbitWeylDescentStatement : Prop :=
  ClosedWeylDescentStatement (chosenLeviModel t.1) (chosenLeviModel t'.1)
    (d t.1) (d t'.1) (hCentralizer t.1) (hCentralizer t'.1) (base t) (rs t.1) (rs t'.1) hk D

set_option hygiene false in
local notation "Family" n:max => ComparisonFamily (chosenLeviModel t.1) (d t.1)
  (hCentralizer t.1) n (base t)
set_option hygiene false in
local notation "Actual" n:max T:max => IsActualFamily (chosenLeviModel t.1) (d t.1) (d t'.1)
  (hCentralizer t.1) n (base t) (rs t.1) (rs t'.1) hk D T
set_option hygiene false in
local notation "RealizesAt" n:max T:max L:max => Realizes (chosenLeviModel t.1) (chosenLeviModel t'.1)
  (d t.1) (d t'.1) (hCentralizer t.1) n (base t) T L

variable (hw : HasWeylRepresentatives i (d t.1).compact.toSubgroup)
  (hD : HasIntrinsicSourceNormalization (d t.1) (base t) (rs t.1) D)
  (hdesc : OrbitWeylDescentStatement hG a ha mu d rs t t' hk D)

set_option hygiene false in
local notation "lift" => compactWeylLift (q := t'.1) (d t.1) (hCentralizer t.1) hw

include hD hdesc in
omit [∀ p, BorelSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))] in
private theorem comparisonRealization :
    QuotientRealization (chosenLeviModel t.1) (chosenLeviModel t'.1)
      (d t.1) (d t'.1) (hCentralizer t.1) (hCentralizer t'.1) (base t) (rs t.1) (rs t'.1)
      hk D lift :=
  (hdesc hD).2.2.2 lift

set_option hygiene false in
local notation "comparison" => comparisonRealization hG a ha mu d rs t t' hk D hw hD hdesc
set_option hygiene false in
local notation "targetOrbit" w:max hn:max => compactLift_targetOrbit hG a ha mu d rs t t' w _ hn

/-- At a qualifying Weyl class, the certified actual smooth comparison in the intrinsic target orbit. -/
def normalizedWeylSection (w : OW) : Sections t ≃ₗ[ℂ] Sections t' :=
  (Classical.choose comparison w.val).trans
    (inTargetBase (lift w.val).val (targetOrbit w (lift w.val).property)).symm

/-- The same intrinsic section is obtained at every certified compact lift. -/
theorem normalizedWeylSection_eq_of_realizes
    (w : OW) (n : Lift) (hn : classOf n = w.val)
    (T : Family n) (U : Sections t ≃ₗ[ℂ] smoothOrbitSections (chosenLeviModel t'.1) (d t'.1) (piConj n))
    (hT : Actual n T) (hU : RealizesAt n T U) (v : Sections t) :
    normalizedWeylSection hG a ha mu d rs t t' hk D hw hD hdesc w v =
      (inTargetBase n (targetOrbit w hn)).symm (U v) := by
  let n' := (lift w.val).val
  have hn' := (lift w.val).property
  let E := inTargetBase n (targetOrbit w hn)
  let E' := inTargetBase n' (targetOrbit w hn')
  apply E'.injective
  calc
    E' (normalizedWeylSection hG a ha mu d rs t t' hk D hw hD hdesc w v) =
        Classical.choose comparison w.val v := E'.apply_symm_apply _
    _ = recenterTarget (chosenLeviModel t'.1) (d t.1) (d t'.1) (hCentralizer t.1)
        (hCentralizer t'.1) (base t) n n' (hn.trans hn'.symm) (U v) :=
      ((Classical.choose_spec comparison).2 w.val n hn T U hT hU v).symm
    _ = E' (E.symm (U v)) := by
      let rebase := recenterTarget (chosenLeviModel t'.1) (d t.1) (d t'.1) (hCentralizer t.1)
        (hCentralizer t'.1) (base t) n n' (hn.trans hn'.symm)
      exact (congrArg rebase (E.apply_symm_apply (U v)).symm).trans
        (recenterTarget_compactLiftTargetBaseEquiv hG a ha mu d rs t t'
          n n' (hn.trans hn'.symm) (targetOrbit w hn) (targetOrbit w hn') (E.symm (U v)))

/-- Evaluation in the represented fiber is exactly the actual normalized coefficient comparison. -/
theorem normalizedWeylSection_realizes
    (w : OW) (n : Lift) (hn : classOf n = w.val)
    (T : Family n) (U : Sections t ≃ₗ[ℂ] smoothOrbitSections (chosenLeviModel t'.1) (d t'.1) (piConj n))
    (hT : Actual n T) (hU : RealizesAt n T U) (v : Sections t) (A : Rep t) :
    HEq ((normalizedWeylSection hG a ha mu d rs t t' hk D hw hD hdesc w v).val
      (compactLiftTargetRepresentative hG a ha mu d rs t t' n (targetOrbit w hn) A))
      (T A (v.val A)) := by
  let E := inTargetBase n (targetOrbit w hn)
  let B := compactLiftTargetRepresentative hG a ha mu d rs t t' n (targetOrbit w hn) A
  have hsection := normalizedWeylSection_eq_of_realizes hG a ha mu d rs t t'
    hk D hw hD hdesc w n hn T U hT hU v
  have heval := congrArg (fun f : Sections t' => f.val B) hsection
  have hbase := compactLiftTargetBaseEquiv_apply hG a ha mu d rs t t'
    n (targetOrbit w hn) (E.symm (U v)) A
  have hcancel := congrArg
    (fun f : smoothOrbitSections (chosenLeviModel t'.1) (d t'.1) (piConj n) => f.val (AConj n A))
    (E.apply_symm_apply (U v))
  exact (heq_of_eq (heval.trans (hbase.symm.trans hcancel))).trans (hU v A)

/-- The selected section comparison uses an actual normalized family at the selected lift. -/
theorem normalizedWeylSection_hasActualFamily (w : OW) :
    ∃ T : Family (lift w.val).val, Actual (lift w.val).val T ∧
      ∀ (v : Sections t) (A : Rep t),
        HEq ((normalizedWeylSection hG a ha mu d rs t t' hk D hw hD hdesc w v).val
          (compactLiftTargetRepresentative hG a ha mu d rs t t' (lift w.val).val
            (targetOrbit w (lift w.val).property) A)) (T A (v.val A)) := by
  obtain ⟨_, T, hT, hU⟩ := (Classical.choose_spec comparison).1 w.val
  exact ⟨T, hT, fun v A => normalizedWeylSection_realizes hG a ha mu d rs t t'
    hk D hw hD hdesc w (lift w.val).val (lift w.val).property T
    (Classical.choose comparison w.val) hT hU v A⟩

/-- Evaluate in the requested target fiber by canonical transport of the inverse constituent. -/
theorem normalizedWeylSection_at_inverse
    (w : OW) (n : Lift) (hn : classOf n = w.val)
    (T : Family n) (U : Sections t ≃ₗ[ℂ] smoothOrbitSections (chosenLeviModel t'.1) (d t'.1) (piConj n))
    (hT : Actual n T) (hU : RealizesAt n T U) (v : Sections t) (B : Rep t') :
    let A := compactLiftSourceRepresentative hG a ha mu d rs t t' w n hn B
    let e := compactLiftInverseInducingEquiv hG a ha mu d rs t t' w n hn B
    (normalizedWeylSection hG a ha mu d rs t t' hk D hw hD hdesc w v).val B =
      productInducedCoefficientTransport (decomposition t'.1) (isClosed_radical t'.1) e (T A (v.val A)) := by
  dsimp only
  let A := compactLiftSourceRepresentative hG a ha mu d rs t t' w n hn B
  let B₀ := compactLiftTargetRepresentative hG a ha mu d rs t t' n (targetOrbit w hn) A
  let e := compactLiftInverseInducingEquiv hG a ha mu d rs t t' w n hn B
  let f := normalizedWeylSection hG a ha mu d rs t t' hk D hw hD hdesc w v
  have h := eq_of_heq (normalizedWeylSection_realizes hG a ha mu d rs t t'
    hk D hw hD hdesc w n hn T U hT hU v A)
  exact (f.property.1 B₀ B e).trans (congrArg
    (productInducedCoefficientTransport (decomposition t'.1) (isClosed_radical t'.1) e) h)

end CertifiedComparison

section FourierWeylSum

variable {K : OpenSubgroup (rationalPoints G)} (hK : IsCompact (K : Set (rationalPoints G)))

/-- The actual common-compact scalar of Waldspurger VII.2.1 and VII.2.2(ii). -/
def sourceWeylScale (p : SemistandardSpectralIndex i) : ℝ :=
  SourceConstants.gammaReal (rs p) K hK * (SourceConstants.cReal (rs p) K hK) ^ 2

variable (hi : IsMaximalSplitTorus i)

/-- The normalized coefficient sum evaluated in one actual target fiber. -/
def fourierWeylSum (t t' : Theta) (hk : (d t'.1).compact = (d t.1).compact)
    (D : LeviNormalization (rs t.1).hom (dynamicInducing (rs t.1) (base t).obj))
    (hw : HasWeylRepresentatives i (d t.1).compact.toSubgroup)
    (hD : HasIntrinsicSourceNormalization (d t.1) (base t) (rs t.1) D)
    (hdesc : OrbitWeylDescentStatement hG a ha mu d rs t t' hk D)
    (v : Sections t) (A : Rep t') : orbitFiber A.val :=
  letI := hG.finite_relativeWeylGroup i hi
  sourceWeylScale hG rs hK t.1 • orbitWeylSum a ha mu t t' (hCentralizer t.1)
    (fun w => (normalizedWeylSection hG a ha mu d rs t t' hk D hw hD hdesc w v).val A)

/-- The Fourier expression vanishes when no Weyl class passes the constituent test. -/
theorem fourierWeylSum_of_isEmpty (t t' : Theta) (hk : (d t'.1).compact = (d t.1).compact)
    (D : LeviNormalization (rs t.1).hom (dynamicInducing (rs t.1) (base t).obj))
    (hw : HasWeylRepresentatives i (d t.1).compact.toSubgroup)
    (hD : HasIntrinsicSourceNormalization (d t.1) (base t) (rs t.1) D)
    (hdesc : OrbitWeylDescentStatement hG a ha mu d rs t t' hk D)
    [IsEmpty (OrbitWeylTransporters a ha mu t t' (hCentralizer t.1))]
    (v : Sections t) (A : Rep t') :
    fourierWeylSum hG a ha mu d rs hK hi t t' hk D hw hD hdesc v A = 0 := by
  let _ := hG.finite_relativeWeylGroup i hi
  simp only [fourierWeylSum, orbitWeylSum_of_isEmpty, smul_zero]

variable [∀ p, IsAffine (T p).X.left] [∀ p, (rationalPoints.map (a p)).range.Normal]
  [∀ p, (mu p).IsInvInvariant]
  (hindex : ∀ p, (RenardCartan.splitValuationImage (a p)).FiniteIndex)
  (Q : ∀ t : Theta, OrbitPacketData (rs t.1) (base t))
  {nu : cocharacterLattice S}
  (hPK : IsIwasawaPair (standardParabolicPoints i nu ∅) (K : Subgroup (rationalPoints G)))
  {N : ℕ} [Nonempty (Fin N)] (rho : MatrixRepresentation G (Fin N))
  (hnu : IsGenericCocharacter i nu)
  (hsw : SquareIntegrableWeight (RationalDynamicSource.ambientHaar K hK)
    (rationalXi hK hPK) (rationalHeight (F := F) rho))
  (hdelta : ∀ p : SemistandardSpectralIndex i, ModularNormalization p)
  (hT : ∀ (p : SemistandardSpectralIndex i)
    (A : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p)),
    IsSquareIntegrableModCentralSubgroup (Center p) (Central p) A.obj.representation (mu p) →
    HasTemperedCoefficients (rationalXi hK hPK) (rationalHeight (F := F) rho)
      ((normalizedInductionFunctor (decomposition p) (isClosed_radical p)).obj A.obj).representation)

set_option hygiene false in
local notation "SourceCompact" => SourceCompactCompatibility hG a ha mu d rs Q (nu := nu) (K := K)

omit [∀ p, BorelSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))]
  [∀ p, IsAffine (T p).X.left] [∀ p, (rationalPoints.map (a p)).range.Normal]
  [∀ p, (mu p).IsInvInvariant] in
/-- Every source Weyl class has an actual representative in the compact picture of each Levi. -/
theorem hasWeylRepresentatives_of_sourceCompact (hsource : SourceCompact)
    (p : SemistandardSpectralIndex i) : HasWeylRepresentatives i (d p).compact.toSubgroup := by
  rw [hsource.2.1 p]
  exact hsource.1.2.2.1

set_option hygiene false in
local notation "Fourier" => (
  letI := Langlands.Haar.isMulRightInvariant_of_modularCharacter_eq_one
    (ambient_modularCharacter hG) (RationalDynamicSource.ambientHaar K hK)
  rationalSemistandardFourierFamily hG hi hnu hK hPK rho hsw a ha mu d hdelta hT)
set_option hygiene false in
local notation "Mem" => ComponentSchwartzMembershipStatement hG a ha mu d rs hindex Q hK hPK rho

/-- Waldspurger VII.2.1 at every square-integrable inducing object of the source Levi. -/
def FourierWeylSumStatement : Prop :=
  ∀ (hsource : SourceCompact) (hcompact : IsSourceCompactAt i K.toSubgroup)
    (hhaar : ∀ p, SourceLeviQuotientHaar a mu (K := K) p) (hmem : Mem)
    (t : Theta) (v : Sections t)
    (A : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi t.1))
    (hA : IsSquareIntegrableModCentralSubgroup (Center t.1) (Central t.1)
      A.obj.representation (mu t.1))
    (D : LeviNormalization (rs t.1).hom (dynamicInducing (rs t.1) (base t).obj)),
    let O := Quotient.mk _ (discreteSeriesClass (Center t.1) (Central t.1) (mu t.1) A hA)
    let t' : Theta := ⟨t.1, O⟩
    ∀ (hmatch : LeviNormalizationMatches hG a ha mu rs t D)
      (hdesc : OrbitWeylDescentStatement hG a ha mu d rs t t' rfl D),
      let B := orbitRepresentativeMember (chosenLeviModel t.1) (a t.1) (ha t.1) (mu t.1) O A hA rfl
      Fourier (schwartzPacket hG a ha mu d rs hindex Q hK hPK rho hmem t v) t' B =
        fourierWeylSum hG a ha mu d rs hK hi t t' rfl D
          (hasWeylRepresentatives_of_sourceCompact hG a ha mu d rs Q hsource t.1)
          (hasIntrinsicSourceNormalization_of_commonCompact hG a ha mu d rs t D
            (hsource.2.1 t.1) hcompact (hhaar t.1) hmatch)
          hdesc v B

end FourierWeylSum

end Langlands.HarishChandraSchwartz.RationalSemistandard.WavePacketPairing

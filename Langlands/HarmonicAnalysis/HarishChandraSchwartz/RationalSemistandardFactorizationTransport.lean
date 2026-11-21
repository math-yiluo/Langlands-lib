import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardInvariantSynthesis
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardAssociationFormula
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardAssociationMean

/-! # VI.3.2 factorization from actual one-orbit transport -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 900000

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz.RationalSemistandard.GlobalSynthesis

open Association InvariantComparison

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
  [∀ p, IsAffine (Z p).X.left]
  {a : ∀ p, (Z p).toGrp ⟶ (chosenLeviModel p).scheme}
  {ha : ∀ p, IsSplitComponent (a p)}
  [∀ p, ((chosenLeviModel p).splitCenter (a p)).Normal]
  [∀ p, (rationalPoints.map (a p)).range.Normal]
  [∀ p, MeasurableSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))]
  [∀ p, BorelSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))]
  {mu : ∀ p, Measure (levi p ⧸ (chosenLeviModel p).splitCenter (a p))}
  [∀ p, (mu p).IsHaarMeasure]
  {d : ∀ p : SemistandardSpectralIndex i, CompactData p}
  {hG : IsConnectedReductive G}
  (C : WeylSectionComparisonData.{u, uV} a ha mu d hG)
  (hi : IsMaximalSplitTorus i)
  (hD : SemistandardSpectralDynamicCoverageStatement.{u})
  (hfin : SemistandardSpectralFiberFinitenessStatement.{u})
  (hindex : ∀ p, (RenardCartan.splitValuationImage (a p)).FiniteIndex)
  (Q : ∀ t : RationalSemistandardTheta.{u, uV} a ha mu,
    OrbitPacketData (C.presentation t.1) (base a ha mu t))

set_option hygiene false in
set_option quotPrecheck false in
local notation "Θ" => RationalSemistandardTheta.{u, uV} a ha mu
set_option hygiene false in
set_option quotPrecheck false in
local notation "Smooth" => rationalSemistandardThetaSmoothSections.{u, uV} a ha mu d
set_option hygiene false in
local notation "component" => rationalSemistandardThetaComponent a ha mu d
set_option hygiene false in
local notation "SectionAt" => rationalSemistandardThetaComponentSpace a ha mu d
set_option hygiene false in
local notation "packet" => componentPacket hG a ha mu d C.presentation hindex Q

/-- Evaluation at an ambient point of the actual component synthesis. -/
def componentPacketEvaluation (g : rationalPoints G) (t : Θ) : SectionAt t →ₗ[ℂ] ℂ :=
  (LinearMap.proj g).comp (packet t)

set_option hygiene false in
local notation "evaluation" => componentPacketEvaluation C hindex Q
set_option hygiene false in
local notation "A" => Average.smoothAverage C hi hD hfin

variable (hE : C.CoefficientTransportStatement) (hDensity : C.DensityTransportStatement Q)
  (hQ : ∀ t : Θ, (Q t).compact = (d t.1).compact)

include hE hDensity hQ in
set_option maxHeartbeats 1800000 in
/-- After the exact one-orbit comparison, each averaged packet value is
the arithmetic mean of the original values over its association class. -/
theorem averagedPacket_eq_associationMean (f : Smooth) (g : rationalPoints G) (t : Θ) :
    packet t (component t (A f)) g =
      associationMean a ha mu (fun q => packet q (component q f) g) t := by
  classical
  let T := Average.Pair C hi hD t
  let v : Θ → ℂ := fun q => evaluation g q (component q f)
  let target := weylParabolicTarget hG hi hD a ha mu t (C.centralizer_le t.1)
  let invComparison (x : T) :=
    (C.smoothComparison t x.2.val (Average.lift C hi hD t x)).symm
      (component (C.target t x.2.val (Average.lift C hi hD t x)) f)
  have hcomponent : component t (A f) = Average.smoothComponent C hi hD hfin f t :=
    Subtype.ext (Average.smoothComponent_val C hi hD hfin f t).symm
  have hpoint (x : T) : packet t (invComparison x) g =
      packet (target x) (component (target x) f) g := by
    let n := Average.lift C hi hD t x
    let q := C.target t x.2.val n
    have hcarry : packet t (invComparison x) = packet q (component q f) :=
      C.componentPacket_transport_symm t x.2.val n Q hindex hE hDensity hQ (component q f)
    have htarget := congrArg (fun y : Θ => packet y (component y f))
      (Average.target_eq_weylParabolicTarget C hi hD t x)
    exact congrFun (hcarry.trans htarget) g
  let : Finite T := finite_weylParabolicPair hG hi hD hfin t.1.toLevi (C.centralizer_le t.1)
  let : Fintype T := Fintype.ofFinite T
  have hsum : (∑ x ∈ Average.pairs C hi hD hfin t, v (target x)) =
      ∑ᶠ x : T, v (target x) :=
    (finsum_eq_sum_of_fintype (fun x : T => v (target x))).symm
  have hscale : Average.scale t = (Nat.card T : ℂ)⁻¹ := by
    rw [Average.scale, card_weylParabolicPair hG hi hD t.1.toLevi (C.centralizer_le t.1),
      Nat.cast_mul]
  change evaluation g t (component t (A f)) = associationMean a ha mu v t
  calc
    _ = evaluation g t (Average.smoothComponent C hi hD hfin f t) :=
      congrArg (evaluation g t) hcomponent
    _ = Average.scale t * ∑ x ∈ Average.pairs C hi hD hfin t, evaluation g t (invComparison x) := by
      rw [Average.smoothComponent, map_smul, map_sum, smul_eq_mul]
    _ = (Nat.card T : ℂ)⁻¹ * ∑ᶠ x : T, v (target x) :=
      congrArg₂ (· * ·) hscale ((Finset.sum_congr rfl (fun x _ => by
        change packet t (invComparison x) g = packet (target x) (component (target x) f) g
        exact hpoint x)).trans hsum)
    _ = _ := weylParabolicMean_eq_associationMean a ha mu hG hi hfin hD t (C.centralizer_le t.1) v

variable (K0 : OpenSubgroup (rationalPoints G)) (hK0 : IsCompact (K0 : Set (rationalPoints G)))

set_option hygiene false in
local notation "weight" => sourceWeight hG C.presentation K0 hK0
set_option hygiene false in
local notation "synthesis" => weightedSynthesis hG a ha mu d C.presentation hindex Q K0 hK0

private theorem synthesis_eq_finsum_packetEvaluation (f : Smooth) (g : rationalPoints G) :
    synthesis f g = ∑ᶠ t, (weight t.1 : ℂ) * evaluation g t (component t f) := by
  let v : Θ → ℂ := fun t => evaluation g t (component t f)
  have hs : Function.support v ⊆ FiniteSupportSections.support f.val :=
    FiniteSupportSections.linearSummand_support_subset SectionAt (fun t => evaluation g t) f
  refine (weightedSynthesis_apply hG a ha mu d C.presentation hindex Q K0 hK0 f g).trans ?_
  symm
  apply finsum_eq_sum_of_support_subset (fun t => (weight t.1 : ℂ) * v t)
  intro t ht
  exact f.property.2.mem_toFinset.mpr
    (hs (fun h => ht ((congrArg ((weight t.1 : ℂ) * ·) h).trans (mul_zero _))))

variable (hI : SourceConstantParabolicIndependenceStatement (i := i) hG)
  (nu : cocharacterLattice S) (hnu : IsGenericCocharacter i nu)
  (hspecial : SpecialCompactProperties F i nu (K0 : Subgroup (rationalPoints G)))
  (hd : ∀ p, (d p).compact = K0) (hQ0 : ∀ t : Θ, (Q t).compact = K0)

include hE hDensity hI hnu hspecial hd hQ0 in
/-- One-orbit source transport and the actual finite geometric classes
imply the raw VI.3.2 equality. -/
theorem factorization_of_transport :
    FactorizationStatement hG a ha mu d C.presentation hindex Q K0 hK0 C hi hD hfin := by
  intro f
  funext g
  let v : Θ → ℂ := fun t => evaluation g t (component t f)
  let w : Θ → ℂ := fun t => (weight t.1 : ℂ)
  have hcompact (t : Θ) : (Q t).compact = (d t.1).compact := (hQ0 t).trans (hd t.1).symm
  have hfinite : (Function.support v).Finite :=
    FiniteSupportSections.linearSummand_finite SectionAt (fun t => evaluation g t) f
  have hw (t q : Θ) (h : Associated a ha mu t q) : w t = w q :=
    congrArg Complex.ofReal (sourceWeight_eq_of_associated C K0 hK0 hi hD hI nu hnu hspecial h)
  calc
    synthesis f g = ∑ᶠ t, w t * v t := synthesis_eq_finsum_packetEvaluation C hindex Q K0 hK0 f g
    _ = ∑ᶠ t, w t * associationMean a ha mu v t :=
      (finsum_mul_associationMean a ha mu hG hi hfin
        (semistandardLeviCentralizerContainment_of_dynamicCoverage hD) v w hfinite hw).symm
    _ = ∑ᶠ t, w t * evaluation g t (component t (A f)) := by
      apply finsum_congr
      intro t
      exact congrArg (w t * ·) ((averagedPacket_eq_associationMean C hi hD hfin hindex Q
        hE hDensity hcompact f g t).symm)
    _ = synthesis (A f) g := (synthesis_eq_finsum_packetEvaluation C hindex Q K0 hK0 (A f) g).symm

end Langlands.HarishChandraSchwartz.RationalSemistandard.GlobalSynthesis

import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardProperOrbitSymmetry
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardInvariantComparison
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardWeylOrbitMeasure
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardGlobalForm

/-! # Orbit points and measure for the actual normalized comparison -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 700000

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz.RationalSemistandard.WeylSectionComparisonData

open InvariantComparison

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

set_option hygiene false in
set_option quotPrecheck false in
local notation "Θ" => RationalSemistandardTheta.{u, uV} a ha mu

set_option hygiene false in
local notation "M" p:max => chosenLeviModel p
set_option hygiene false in
local notation "Center" p:max => (M p).splitCenter (a p)
set_option hygiene false in
local notation "central" p:max => (M p).splitCenter_le_center (a p) (ha p)

variable (t : Θ)

/-- The square-integrability witness on the actual chosen inducing object. -/
abbrev squareIntegrableBase :=
  orbitRepresentative_isSquareIntegrable (M t.1) (a t.1) (ha t.1) (mu t.1) t.2

/-- The actual class of the inducing object used by the component integral. -/
abbrev discreteSeriesBase :=
  discreteSeriesClass (Center t.1) (central t.1) (mu t.1) (base a ha mu t)
    (squareIntegrableBase t)

variable (C : WeylSectionComparisonData.{u, uV} a ha mu d hG)
  (q : SemistandardSpectralIndex i) (n : C.Lift t q)

set_option hygiene false in
local notation "tq" => C.target t q n
set_option hygiene false in
local notation "hc" => liftConjugatesLevi (C.centralizer_le t.1) (d t.1).compact n
set_option hygiene false in
local notation "eD" => Association.conjugateDiscreteSeriesClass hc (M t.1) (M q)
  (a t.1) (ha t.1) (a q) (ha q) (mu t.1) (mu q)

private theorem conjugateBaseClass_mk :
    (Quotient.mk _ (eD (discreteSeriesBase t)) : OrbitClass (M q) (a q) (ha q) (mu q)) =
      Quotient.mk _ (discreteSeriesBase tq) := by
  change Association.conjugateOrbit hc (M t.1) (M q) (a t.1) (ha t.1)
    (a q) (ha q) (mu t.1) (mu q) (Quotient.mk _ (discreteSeriesBase t)) = _
  rw [mk_discreteSeriesClass_orbitRepresentative]
  exact (mk_discreteSeriesClass_orbitRepresentative (M q) (a q) (ha q) (mu q) (tq).2).symm

/-- The orbit homeomorphism belonging to the very same compact Weyl lift
used by the coefficient comparison. -/
def orbitPointComparison :
    GlobalForm.OrbitPoint a ha mu t ≃ₜ GlobalForm.OrbitPoint a ha mu tq :=
  SourceMeasure.orbitConjugationRecentered hc (M t.1) (M q)
    (a t.1) (ha t.1) (a q) (ha q) (mu t.1) (mu q)
    (discreteSeriesBase t) (conjugateBaseClass_mk t C q n)

/-- The orbit homeomorphism and the comparison of all actual inducing
representatives agree at every representative. -/
theorem orbitPointComparison_representative (A : Representatives a ha mu t) :
    orbitPointComparison t C q n (GlobalSynthesis.componentOrbitPoint a ha mu t A) =
      GlobalSynthesis.componentOrbitPoint a ha mu tq (C.representative t q n A) := by
  apply Subtype.ext
  refine (SourceMeasure.orbitConjugationRecentered_val hc (M t.1) (M q)
    (a t.1) (ha t.1) (a q) (ha q) (mu t.1) (mu q) (discreteSeriesBase t)
    (conjugateBaseClass_mk t C q n) (GlobalSynthesis.componentOrbitPoint a ha mu t A)).trans ?_
  apply Subtype.ext
  let x : SmoothDualClass.{0, u, uV} (k := ℂ) (G := levi t.1) := Quotient.mk _ A.val
  change SmoothDualClass.pullback (Association.leviPointConjugation hc).symm x =
    SmoothDualClass.pullback (WeylOrbits.leviPullback (C.centralizer_le t.1) (d t.1).compact n) x
  exact congrArg (fun e : levi q ≃ₜ* levi t.1 => SmoothDualClass.pullback e x)
    (leviPullback_eq (C.centralizer_le t.1) (d t.1).compact n).symm

variable [∀ p, IsAffine (Z p).X.left] [∀ p, (rationalPoints.map (a p)).range.Normal]
  (hindex : ∀ p, (RenardCartan.splitValuationImage (a p)).FiniteIndex)

/-- The comparison of the indexed orbit points preserves the source measure. -/
theorem orbitPointComparison_measurePreserving :
    MeasurePreserving (orbitPointComparison t C q n)
      (GlobalSynthesis.componentOrbitMeasure a ha mu hindex t) (GlobalSynthesis.componentOrbitMeasure a ha mu hindex tq) :=
  ⟨(orbitPointComparison t C q n).continuous.measurable,
    SourceMeasure.normalizedOrbitMeasure_map_conjugationRecentered hc (M t.1) (M q)
      (a t.1) (ha t.1) (a q) (ha q) (mu t.1) (mu q) (discreteSeriesBase t)
      (conjugateBaseClass_mk t C q n) (hindex t.1) (hindex q)⟩

end Langlands.HarishChandraSchwartz.RationalSemistandard.WeylSectionComparisonData

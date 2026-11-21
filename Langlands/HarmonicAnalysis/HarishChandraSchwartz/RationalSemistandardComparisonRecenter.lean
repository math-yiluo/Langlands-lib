import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardOrbitConjugation
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardWeylOrbits

/-! # Recenter the actual Weyl comparison at the intrinsic target index -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz.RationalSemistandard.InvariantComparison

open Association WeylOrbits

attribute [local instance]
  rationalWeightsIsAffine rationalWeightsTopology rationalWeightsTopologicalGroup
  rationalWeightsT2Field rationalWeightsLocallyCompact rationalWeightsMeasurableSpace
  rationalWeightsBorelSpace rationalInducedSecondCountable rationalInducedT2
  rationalInducedNonarchimedean

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G}

section LeviConjugation

variable {p q : SemistandardSpectralIndex i}
  (hP : torusCentralizer i ≤ p.levi) (K : OpenSubgroup (rationalPoints G))
  (n : CompactLift (p := p) (q := q) hP K)

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
/-- The lift in the normalized comparison gives the same literal Levi
conjugation as the geometric association of the full indices. -/
theorem liftConjugatesLevi : ConjugatesLevi n.val p q :=
  (SubgroupFunctor.eq_comap_iso_iff (G.innerIso n.val)).mpr (conjugateLevi_eq hP K n)

/-- The inducing map is inverse conjugation by the very same ambient point. -/
theorem leviPullback_eq : leviPullback hP K n = (leviPointConjugation (liftConjugatesLevi hP K n)).symm := by
  apply ContinuousMulEquiv.ext
  intro x
  apply Subtype.ext
  rfl

end LeviConjugation

variable {Z : SemistandardSpectralIndex i → CommGroupScheme (Spec (CommRingCat.of F))}
  (a : ∀ p, (Z p).toGrp ⟶ (chosenLeviModel p).scheme)
  (ha : ∀ p, IsSplitComponent (a p))
  [∀ p, ((chosenLeviModel p).splitCenter (a p)).Normal]
  [∀ p, MeasurableSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))]
  [∀ p, BorelSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))]
  (mu : ∀ p, Measure (levi p ⧸ (chosenLeviModel p).splitCenter (a p)))
  [∀ p, (mu p).IsHaarMeasure]

/-- The chosen actual inducing object in the orbit of a full index. -/
abbrev base (t : RationalSemistandardTheta.{u, uV} a ha mu) :=
  orbitRepresentative (chosenLeviModel t.1) (a t.1) (ha t.1) (mu t.1) t.2

/-- All actual inducing objects in the indexed unitary orbit. -/
abbrev Representatives (t : RationalSemistandardTheta.{u, uV} a ha mu) :=
  UnitaryOrbitRepresentative (chosenLeviModel t.1).normCharacters (base a ha mu t)

variable (d : ∀ p : SemistandardSpectralIndex i, CompactData p)
  (t : RationalSemistandardTheta.{u, uV} a ha mu) (q : SemistandardSpectralIndex i)
  (hP : torusCentralizer i ≤ t.1.levi)
  (n : CompactLift (p := t.1) (q := q) hP (d t.1).compact)

set_option hygiene false in
local notation "K" => (d t.1).compact
set_option hygiene false in
local notation "π" => base a ha mu t
set_option hygiene false in
local notation "πg" => conjugateBase hP K n π
set_option hygiene false in
local notation "m" => chosenLeviModel t.1
set_option hygiene false in
local notation "mq" => chosenLeviModel q

local notation "hc" => liftConjugatesLevi hP K n

include n in
/-- The actual target orbit at the specified parabolic. -/
def targetIndex : RationalSemistandardTheta.{u, uV} a ha mu :=
  conjugateFullIndex a ha mu t q hc

local notation "tq" => targetIndex a ha mu d t q hP n

/-- This target is the actual orbit transported by the Weyl quotient element. -/
theorem weylTransports_targetIndex :
    WeylTransports a ha mu (weylElement hP K n).val t tq :=
  ⟨n.val, rfl, orbitConjugates_conjugateFullIndex a ha mu t q hc⟩

private def transportedDiscreteSeries :
    DiscreteSeriesClass.{u, uV} ((mq).splitCenter (a q))
      ((mq).splitCenter_le_center (a q) (ha q)) (mu q) :=
  conjugateDiscreteSeriesClass hc m mq (a t.1) (ha t.1) (a q) (ha q) (mu t.1) (mu q)
    (discreteSeriesClass ((m).splitCenter (a t.1)) ((m).splitCenter_le_center (a t.1) (ha t.1))
      (mu t.1) π (orbitRepresentative_isSquareIntegrable m (a t.1) (ha t.1) (mu t.1) t.2))

private theorem transportedDiscreteSeries_val :
    (transportedDiscreteSeries a ha mu d t q hP n).val =
      (Quotient.mk _ πg : SmoothDualClass.{0, u, uV} (k := ℂ) (G := levi q)) := by
  let c : SmoothDualClass.{0, u, uV} (k := ℂ) (G := levi t.1) := Quotient.mk _ π
  change SmoothDualClass.pullback (leviPointConjugation hc).symm c =
    SmoothDualClass.pullback (leviPullback hP K n) c
  exact congrArg (fun e : levi q ≃ₜ* levi t.1 => SmoothDualClass.pullback e c)
    (leviPullback_eq hP K n).symm

private theorem targetBase_squareIntegrable :
    IsSquareIntegrableModCentralSubgroup ((mq).splitCenter (a q))
      ((mq).splitCenter_le_center (a q) (ha q)) (πg).obj.representation (mu q) := by
  have h := (transportedDiscreteSeries a ha mu d t q hP n).property
  rw [transportedDiscreteSeries_val] at h
  exact h

private theorem targetBase_mem :
    (Quotient.mk _ (discreteSeriesClass ((mq).splitCenter (a q))
      ((mq).splitCenter_le_center (a q) (ha q)) (mu q) πg
      (targetBase_squareIntegrable a ha mu d t q hP n)) : OrbitClass mq (a q) (ha q) (mu q)) = (tq).2 := by
  have hd : discreteSeriesClass ((mq).splitCenter (a q))
      ((mq).splitCenter_le_center (a q) (ha q)) (mu q) πg
      (targetBase_squareIntegrable a ha mu d t q hP n) =
      transportedDiscreteSeries a ha mu d t q hP n :=
    Subtype.ext (transportedDiscreteSeries_val a ha mu d t q hP n).symm
  rw [hd]
  change conjugateOrbit hc m mq (a t.1) (ha t.1) (a q) (ha q) (mu t.1) (mu q)
    (Quotient.mk _ _) = _
  rw [mk_discreteSeriesClass_orbitRepresentative]
  rfl

/-- The conjugate of the chosen source object belongs to the actual target orbit. -/
def targetBaseMember : Representatives a ha mu tq :=
  orbitRepresentativeMember mq (a q) (ha q) (mu q) (tq).2 πg
    (targetBase_squareIntegrable a ha mu d t q hP n) (targetBase_mem a ha mu d t q hP n)

/-- The literal conjugate inducing object, indexed in the chosen target orbit. -/
def targetRepresentative (A : Representatives a ha mu t) : Representatives a ha mu tq :=
  (unitaryOrbitRepresentativeBaseEquiv (mq).normCharacters (base a ha mu tq)
    (targetBaseMember a ha mu d t q hP n)).symm (conjugateRepresentative hP K n m mq π A)

/-- Smooth recentering to the conjugate source base leaves actual coefficient
values in their original fibers. -/
def targetRecenter : rationalSemistandardThetaComponentSpace a ha mu d tq ≃ₗ[ℂ]
    smoothOrbitSections mq (d q) πg :=
  orbitSmoothSectionsBaseEquiv mq (a q) (ha q) (mu q) (d q) (tq).2 πg
    (targetBase_squareIntegrable a ha mu d t q hP n) (targetBase_mem a ha mu d t q hP n)

/-- The value of the comparison in the chosen target orbit is the very same
value at the actual conjugate object. -/
theorem targetRecenter_symm_apply
    (v : smoothOrbitSections mq (d q) πg) (A : Representatives a ha mu t) :
    ((targetRecenter a ha mu d t q hP n).symm v).val
      (targetRepresentative a ha mu d t q hP n A) =
      v.val (conjugateRepresentative hP K n m mq π A) := rfl

end Langlands.HarishChandraSchwartz.RationalSemistandard.InvariantComparison

import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardThetaParts
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalLocalOrbitFiniteness
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCompactOpenNormalRefinement

/-! # Actual full semistandard fixed indices and local Levi finiteness -/

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

namespace RationalSemistandard

local instance supportModelAffine (p : SemistandardSpectralIndex i) (m : LeviModel p) :
    IsAffine m.scheme.X.left := by
  have := m.reductive.isAffineHom
  exact isAffine_of_isAffineHom m.scheme.X.hom

local instance supportModelFiniteType (p : SemistandardSpectralIndex i) (m : LeviModel p) :
    LocallyOfFiniteType m.scheme.X.hom := by
  have := m.reductive.smooth
  infer_instance

/-- Local VIII.1.2 on a representing scheme of the exact literal Levi. -/
def LeviModel.LocalOrbitFiniteness {p : SemistandardSpectralIndex i} (m : LeviModel p) : Prop :=
  RationalLocalDiscreteSeriesOrbitFinitenessStatement.{u, uV} m.scheme

/-- All semistandard Levis, retaining every actual closed representing model. -/
def AllLeviOrbitFiniteness : Prop :=
  ∀ (p : SemistandardSpectralIndex i) (m : LeviModel p), m.LocalOrbitFiniteness.{u, uV}

/-- Only proper semistandard Levis. This makes no demand at `P = G`. -/
def ProperLeviOrbitFiniteness : Prop :=
  ∀ (p : SemistandardSpectralIndex i), p.IsProper →
    ∀ m : LeviModel p, m.LocalOrbitFiniteness.{u, uV}

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
/-- All-Levi local finiteness restricts to proper Levis. -/
theorem properLeviOrbitFiniteness_of_all
    (h : AllLeviOrbitFiniteness.{u, uV} (i := i)) :
    ProperLeviOrbitFiniteness.{u, uV} (i := i) := fun p _ m => h p m

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
/-- Global VIII.1.2 supplies each local Levi predicate, since its actual model
is connected reductive. The proper-only induction need not use this theorem. -/
theorem allLeviOrbitFiniteness_of_global
    (h : RationalDiscreteSeriesOrbitFinitenessStatement.{u, uV}) :
    AllLeviOrbitFiniteness.{u, uV} (i := i) :=
  fun _ m => rationalLocalDiscreteSeriesOrbitFiniteness_of_global h m.scheme m.reductive

/-- The actual subgroup `M(F) intersect H`, represented inside the literal Levi. -/
def leviLevel (p : SemistandardSpectralIndex i) (H : Subgroup (rationalPoints G)) :
    Subgroup (levi p) := H.comap (levi p).subtype

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
@[simp] theorem mem_leviLevel (p : SemistandardSpectralIndex i)
    (H : Subgroup (rationalPoints G)) (x : levi p) :
    x ∈ leviLevel p H ↔ (x : rationalPoints G) ∈ H := Iff.rfl

omit [LocallyOfFiniteType G.X.hom] in
/-- Closedness of the actual Levi follows from its closed representing inclusion. -/
theorem isClosed_levi (p : SemistandardSpectralIndex i) :
    IsClosed (levi p : Set (rationalPoints G)) :=
  isClosed_rationalPoint_subgroup F p.levi (chosenLeviModel p).inclusion
    (chosenLeviModel p).represents (chosenLeviModel p).closed

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
/-- The literal intersection level is open. -/
theorem isOpen_leviLevel (p : SemistandardSpectralIndex i)
    (H : Subgroup (rationalPoints G)) (hH : IsOpen (H : Set (rationalPoints G))) :
    IsOpen (leviLevel p H : Set (levi p)) := hH.preimage continuous_subtype_val

omit [LocallyOfFiniteType G.X.hom] in
/-- The literal intersection level is compact. -/
theorem isCompact_leviLevel (p : SemistandardSpectralIndex i)
    (H : Subgroup (rationalPoints G)) (hH : IsCompact (H : Set (rationalPoints G))) :
    IsCompact (leviLevel p H : Set (levi p)) :=
  (isClosed_levi p).isClosedEmbedding_subtypeVal.isCompact_preimage hH

/-- Transfer the local VIII.1.2 predicate to the literal Levi, retaining the
specified split center and quotient Haar measure. -/
theorem finite_fixedOrbits_of_local {p : SemistandardSpectralIndex i}
    (m : LeviModel p) (hlocal : m.LocalOrbitFiniteness.{u, uV})
    {A : CommGroupScheme (Spec (CommRingCat.of F))} (a : A.toGrp ⟶ m.scheme)
    (ha : IsSplitComponent a) [(m.splitCenter a).Normal]
    [MeasurableSpace (levi p ⧸ m.splitCenter a)]
    [BorelSpace (levi p ⧸ m.splitCenter a)]
    (mu : Measure (levi p ⧸ m.splitCenter a)) [mu.IsHaarMeasure]
    (H : Subgroup (levi p)) (hHo : IsOpen (H : Set (levi p)))
    (hHc : IsCompact (H : Set (levi p))) :
    (discreteSeriesFixedOrbits (m.splitCenter a) (m.splitCenter_le_center a ha)
      mu m.normCharacters H : Set (OrbitClass.{u, uV} m a ha mu)).Finite := by
  let e := m.pointHomeomorph
  let : TopologicalSpace (rationalPoints m.scheme) := rationalPointTopology F m.scheme.X
  have : NonarchimedeanGroup (rationalPoints m.scheme) :=
    rationalPoints_nonarchimedeanGroup m.scheme
  let B := (rationalPoints.map a).range
  have : B.Normal := B.normal_of_le_center ha.isCentralSplitTorus.isCentral.range_le_center
  let : MeasurableSpace (rationalPoints m.scheme ⧸ B) := borel _
  have : BorelSpace (rationalPoints m.scheme ⧸ B) := ⟨rfl⟩
  have hAB : B.map e.toMulEquiv.toMonoidHom = m.splitCenter a := rfl
  let phi := quotientContinuousMulEquiv e (m.splitCenter a) B hAB
  let muB : Measure (rationalPoints m.scheme ⧸ B) := mu.map phi.symm
  have hmu : muB.map phi = mu :=
    MeasurableEquiv.map_map_symm phi.toHomeomorph.toMeasurableEquiv
  have hfin := hlocal A a ha muB (H.comap e.toMonoidHom)
    (hHo.preimage e.continuous) (e.toHomeomorph.isCompact_preimage.mpr hHc)
  exact finite_discreteSeriesFixedOrbits_of_pullback e m.normCharacters
    (fun chi => (rationalNormCharacters m.scheme chi).toMul)
    (fun chi x => by
      change (rationalNormCharacters m.scheme chi).toMul (e.symm (e x)) = _
      rw [e.symm_apply_apply])
    (m.splitCenter a) (m.splitCenter_le_center a ha) B
    ha.isCentralSplitTorus.isCentral.range_le_center hAB mu muB hmu H hfin

/-- Any actual point of the unitary unramified orbit has the same nonzero
induced-fixed-vector property at levels inside the compact picture. -/
theorem inducedFixedVector_unitaryOrbit_iff (p : SemistandardSpectralIndex i)
    (m : LeviModel p) (d : CompactData p)
    (H : Subgroup (rationalPoints G)) (hHK : H ≤ d.compact.toSubgroup)
    (pi : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p))
    (A : UnitaryOrbitRepresentative m.normCharacters pi) :
    fixedVectors ((normalizedInductionFunctor (decomposition p)
      (isClosed_radical p)).obj A.val.obj).representation H ≠ ⊥ ↔
    fixedVectors ((normalizedInductionFunctor (decomposition p)
      (isClosed_radical p)).obj pi.obj).representation H ≠ ⊥ := by
  obtain ⟨chi, hchi⟩ := A.property
  have h := hasInducedFixedVector_twist_iff (decomposition p) d.compact (isClosed_radical p)
    (isClosed_parabolic p) d.isCompact d.factorization m.normCharacters
    m.continuous_normCharacters d.projection_continuous
    (unitaryUnramifiedInclusion m.normCharacters chi) hHK (Quotient.mk _ pi)
  rw [hchi] at h
  exact h

end RationalSemistandard

section Fixed

variable {T : SemistandardSpectralIndex i → CommGroupScheme (Spec (CommRingCat.of F))}
  (a : ∀ p, (T p).toGrp ⟶ (chosenLeviModel p).scheme)
  (ha : ∀ p, IsSplitComponent (a p))
  [∀ p, ((chosenLeviModel p).splitCenter (a p)).Normal]
  [∀ p, MeasurableSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))]
  (mu : ∀ p, Measure (levi p ⧸ (chosenLeviModel p).splitCenter (a p)))
  [∀ p, (mu p).IsHaarMeasure]

/-- Full actual `Theta^H`, using nonzero fixed vectors of the actual normalized
induced representation for some member of each unitary unramified orbit. -/
def rationalSemistandardThetaFixed (H : Subgroup (rationalPoints G)) :
    Set (RationalSemistandardTheta.{u, uV} a ha mu) :=
  Set.univ.sigma fun p => inducedDiscreteSeriesFixedOrbits (decomposition p)
    (isClosed_radical p) ((chosenLeviModel p).splitCenter (a p))
    ((chosenLeviModel p).splitCenter_le_center (a p) (ha p)) (mu p)
    (chosenLeviModel p).normCharacters H

theorem mem_rationalSemistandardThetaFixed (H : Subgroup (rationalPoints G))
    (t : RationalSemistandardTheta.{u, uV} a ha mu) :
    t ∈ rationalSemistandardThetaFixed.{u, uV} a ha mu H ↔
      t.2 ∈ inducedDiscreteSeriesFixedOrbits (decomposition t.1) (isClosed_radical t.1)
        ((chosenLeviModel t.1).splitCenter (a t.1))
        ((chosenLeviModel t.1).splitCenter_le_center (a t.1) (ha t.1)) (mu t.1)
        (chosenLeviModel t.1).normCharacters H := by
  simp [rationalSemistandardThetaFixed, Set.mem_sigma_iff]

/-- The full fixed-index sets grow when the level shrinks. -/
theorem rationalSemistandardThetaFixed_antitone :
    Antitone (rationalSemistandardThetaFixed.{u, uV} a ha mu) := by
  intro L H hLH t ht
  rw [mem_rationalSemistandardThetaFixed] at ht ⊢
  obtain ⟨w, hw, he⟩ := ht
  refine ⟨w, ?_, he⟩
  change HasInducedFixedVector (decomposition t.1) (isClosed_radical t.1) H w.val at hw
  change HasInducedFixedVector (decomposition t.1) (isClosed_radical t.1) L w.val
  revert hw
  induction w.val using Quotient.inductionOn with
  | h A => exact fun hA => fixedVectors_ne_bot_of_le _ hLH hA

/-- Representative independence within the compact-picture level, by the
published unramified-twist comparison. -/
theorem mem_rationalSemistandardThetaFixed_iff_of_le
    (d : ∀ p : SemistandardSpectralIndex i, CompactData p)
    (H : Subgroup (rationalPoints G)) (t : RationalSemistandardTheta.{u, uV} a ha mu)
    (hHK : H ≤ (d t.1).compact.toSubgroup)
    (pi : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi t.1))
    (hsq : IsSquareIntegrableModCentralSubgroup ((chosenLeviModel t.1).splitCenter (a t.1))
      ((chosenLeviModel t.1).splitCenter_le_center (a t.1) (ha t.1))
      pi.obj.representation (mu t.1))
    (hO : (Quotient.mk _ (discreteSeriesClass ((chosenLeviModel t.1).splitCenter (a t.1))
      ((chosenLeviModel t.1).splitCenter_le_center (a t.1) (ha t.1)) (mu t.1) pi hsq) :
      OrbitClass.{u, uV} (chosenLeviModel t.1) (a t.1) (ha t.1) (mu t.1)) = t.2) :
    t ∈ rationalSemistandardThetaFixed.{u, uV} a ha mu H ↔
      fixedVectors ((normalizedInductionFunctor (decomposition t.1)
        (isClosed_radical t.1)).obj pi.obj).representation H ≠ ⊥ := by
  rw [mem_rationalSemistandardThetaFixed, ← hO]
  exact mk_mem_inducedDiscreteSeriesFixedOrbits_iff (decomposition t.1) (isClosed_radical t.1)
    ((chosenLeviModel t.1).splitCenter (a t.1))
    ((chosenLeviModel t.1).splitCenter_le_center (a t.1) (ha t.1)) (mu t.1)
    (chosenLeviModel t.1).normCharacters (d t.1).compact (isClosed_parabolic t.1)
    (d t.1).isCompact (d t.1).factorization (chosenLeviModel t.1).continuous_normCharacters
    (d t.1).projection_continuous hHK _

/-- The remaining arbitrary-level orbit-independence target. At a level inside
the supplied compact picture the preceding theorem proves this comparison;
no extension to arbitrary compact open levels is hidden in the orbit carrier. -/
def RationalSemistandardFixedOrbitIndependenceStatement : Prop :=
  ∀ (H : Subgroup (rationalPoints G)), IsOpen (H : Set (rationalPoints G)) →
    IsCompact (H : Set (rationalPoints G)) →
    ∀ (t : RationalSemistandardTheta.{u, uV} a ha mu)
      (pi : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi t.1))
      (hsq : IsSquareIntegrableModCentralSubgroup ((chosenLeviModel t.1).splitCenter (a t.1))
        ((chosenLeviModel t.1).splitCenter_le_center (a t.1) (ha t.1))
        pi.obj.representation (mu t.1)),
      (Quotient.mk _ (discreteSeriesClass ((chosenLeviModel t.1).splitCenter (a t.1))
        ((chosenLeviModel t.1).splitCenter_le_center (a t.1) (ha t.1)) (mu t.1) pi hsq) :
        OrbitClass.{u, uV} (chosenLeviModel t.1) (a t.1) (ha t.1) (mu t.1)) = t.2 →
      (t ∈ rationalSemistandardThetaFixed.{u, uV} a ha mu H ↔
        fixedVectors ((normalizedInductionFunctor (decomposition t.1)
          (isClosed_radical t.1)).obj pi.obj).representation H ≠ ⊥)

end Fixed

end Langlands.HarishChandraSchwartz

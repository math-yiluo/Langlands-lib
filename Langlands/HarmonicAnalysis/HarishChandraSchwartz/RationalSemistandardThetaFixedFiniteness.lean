import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardThetaFixed
import Langlands.BruhatTits.SpecialCompact.Properties

/-! # Full and proper VIII.1.3(i), with explicit normal-level comparison -/

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

/-- The exact level condition that the actual Levi projection takes the
parabolic intersection onto the literal Levi intersection. Normality alone
does not imply this identity. -/
def RationalSemistandardLevelProjectionCompatible
    (p : SemistandardSpectralIndex i) (L : Subgroup (rationalPoints G)) : Prop :=
  (L.comap (parabolic p).subtype).map (decomposition p).projection = leviLevel p L

/-- The forward normal-level comparison used by the finiteness argument.
It deliberately does not assert the converse at an arbitrary normal level. -/
def RationalSemistandardNormalLevelFixedComparisonAt
    (p : SemistandardSpectralIndex i) (K : OpenSubgroup (rationalPoints G)) : Prop :=
  ∀ L : CompactOpenSubgroup (rationalPoints G),
    L.toSubgroup ≤ K.toSubgroup → (L.toSubgroup.subgroupOf K.toSubgroup).Normal →
    ∀ A : SmoothRep.{0, u, uV} ℂ (levi p),
      (fixedVectors ((normalizedInductionFunctor (decomposition p)
        (isClosed_radical p)).obj A).representation L.toSubgroup ≠ ⊥ →
        fixedVectors A.representation (leviLevel p L.toSubgroup) ≠ ⊥)

/-- The forward comparison at every full index. -/
def RationalSemistandardNormalLevelFixedComparison
    (K : OpenSubgroup (rationalPoints G)) : Prop :=
  ∀ p : SemistandardSpectralIndex i,
    RationalSemistandardNormalLevelFixedComparisonAt.{u, uV} p K

/-- Only proper parabolics need the forward comparison for proper finiteness. -/
def RationalProperSemistandardNormalLevelFixedComparison
    (K : OpenSubgroup (rationalPoints G)) : Prop :=
  ∀ p : SemistandardSpectralIndex i, p.IsProper →
    RationalSemistandardNormalLevelFixedComparisonAt.{u, uV} p K

/-- The full forward comparison restricts to the proper indices. -/
theorem rationalProperSemistandardNormalLevelFixedComparison_of_full
    (K : OpenSubgroup (rationalPoints G))
    (h : RationalSemistandardNormalLevelFixedComparison.{u, uV} (i := i) K) :
    RationalProperSemistandardNormalLevelFixedComparison.{u, uV} (i := i) K :=
  fun p _ => h p

/-- The two-way comparison is restricted to levels satisfying the explicit
actual Levi-projection identity. No condition on every normal subgroup is
inferred from properties of the containing compact subgroup. -/
def RationalSemistandardAdaptedNormalLevelFixedComparisonAt
    (p : SemistandardSpectralIndex i) (K : OpenSubgroup (rationalPoints G)) : Prop :=
  ∀ L : CompactOpenSubgroup (rationalPoints G),
    L.toSubgroup ≤ K.toSubgroup → (L.toSubgroup.subgroupOf K.toSubgroup).Normal →
    RationalSemistandardLevelProjectionCompatible p L.toSubgroup →
    ∀ A : SmoothRep.{0, u, uV} ℂ (levi p),
      (fixedVectors ((normalizedInductionFunctor (decomposition p)
        (isClosed_radical p)).obj A).representation L.toSubgroup ≠ ⊥ ↔
        fixedVectors A.representation (leviLevel p L.toSubgroup) ≠ ⊥)

/-- The adapted-level equivalence at every full index. -/
def RationalSemistandardAdaptedNormalLevelFixedComparison
    (K : OpenSubgroup (rationalPoints G)) : Prop :=
  ∀ p : SemistandardSpectralIndex i,
    RationalSemistandardAdaptedNormalLevelFixedComparisonAt.{u, uV} p K

/-- The adapted-level equivalence only at proper indices. -/
def RationalProperSemistandardAdaptedNormalLevelFixedComparison
    (K : OpenSubgroup (rationalPoints G)) : Prop :=
  ∀ p : SemistandardSpectralIndex i, p.IsProper →
    RationalSemistandardAdaptedNormalLevelFixedComparisonAt.{u, uV} p K

/-- Full adapted-level comparison restricts to proper indices. -/
theorem rationalProperSemistandardAdaptedNormalLevelFixedComparison_of_full
    (K : OpenSubgroup (rationalPoints G))
    (h : RationalSemistandardAdaptedNormalLevelFixedComparison.{u, uV} (i := i) K) :
    RationalProperSemistandardAdaptedNormalLevelFixedComparison.{u, uV} (i := i) K :=
  fun p _ => h p

/-- Separate cofinal-refinement target for a specified compact subgroup K:
refine each compact open H to a level normal in K and projection-compatible
at every actual index. The topological normal-refinement theorem alone does
not provide the final compatibility clause. The forward-only finiteness
adapters below do not consume this stronger target. -/
def RationalSemistandardAdaptedNormalRefinementStatement
    (K : OpenSubgroup (rationalPoints G)) : Prop :=
  ∀ H : Subgroup (rationalPoints G), IsOpen (H : Set (rationalPoints G)) →
    IsCompact (H : Set (rationalPoints G)) →
    ∃ L : CompactOpenSubgroup (rationalPoints G),
      L.toSubgroup ≤ H ∧ L.toSubgroup ≤ K.toSubgroup ∧
      (L.toSubgroup.subgroupOf K.toSubgroup).Normal ∧
      ∀ p : SemistandardSpectralIndex i,
        RationalSemistandardLevelProjectionCompatible p L.toSubgroup

/-- The forward comparison and the adapted-level equivalence in the source's
special-compact setting. Projection continuity and actual Iwasawa factorization
remain explicit. The equivalence still requires the displayed level condition;
this target does not conclude adapted cofinal refinement. -/
def RationalSemistandardSpecialCompactFixedComparisonStatement
    (nu : cocharacterLattice S) (K : OpenSubgroup (rationalPoints G)) : Prop :=
  IsConnectedReductive G → IsMaximalSplitTorus i → IsGenericCocharacter i nu →
    Langlands.BruhatTits.SpecialCompact.SpecialCompactProperties F i nu K.toSubgroup →
    (∀ p : SemistandardSpectralIndex i, Continuous (decomposition p).projection) →
    (∀ (p : SemistandardSpectralIndex i) (g : rationalPoints G),
      ∃ x : parabolic p, ∃ k : K, g = (x : rationalPoints G) * (k : rationalPoints G)) →
    RationalSemistandardNormalLevelFixedComparison.{u, uV} (i := i) K ∧
      RationalSemistandardAdaptedNormalLevelFixedComparison.{u, uV} (i := i) K

section Families

variable {T : SemistandardSpectralIndex i → CommGroupScheme (Spec (CommRingCat.of F))}
  (a : ∀ p, (T p).toGrp ⟶ (chosenLeviModel p).scheme)
  (ha : ∀ p, IsSplitComponent (a p))
  [∀ p, ((chosenLeviModel p).splitCenter (a p)).Normal]
  [∀ p, MeasurableSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))]
  (mu : ∀ p, Measure (levi p ⧸ (chosenLeviModel p).splitCenter (a p)))
  [∀ p, (mu p).IsHaarMeasure]
  [∀ p, BorelSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))]

omit [∀ p, BorelSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))] in
/-- At a normal level the exact model comparison sends every induced-fixed
orbit into the fixed-orbit set of the actual literal Levi intersection. -/
theorem inducedFixedOrbits_subset_leviFixed
    (K : OpenSubgroup (rationalPoints G))
    (p : SemistandardSpectralIndex i)
    (hcomp : RationalSemistandardNormalLevelFixedComparisonAt.{u, uV} p K) (L : CompactOpenSubgroup (rationalPoints G))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hLN : (L.toSubgroup.subgroupOf K.toSubgroup).Normal) :
    (inducedDiscreteSeriesFixedOrbits (decomposition p) (isClosed_radical p)
      ((chosenLeviModel p).splitCenter (a p))
      ((chosenLeviModel p).splitCenter_le_center (a p) (ha p)) (mu p)
      (chosenLeviModel p).normCharacters L.toSubgroup :
        Set (OrbitClass.{u, uV} (chosenLeviModel p) (a p) (ha p) (mu p))) ⊆
    discreteSeriesFixedOrbits ((chosenLeviModel p).splitCenter (a p))
      ((chosenLeviModel p).splitCenter_le_center (a p) (ha p)) (mu p)
      (chosenLeviModel p).normCharacters (leviLevel p L.toSubgroup) := by
  rintro _ ⟨w, hw, rfl⟩
  refine ⟨w, ?_, rfl⟩
  change HasInducedFixedVector (decomposition p) (isClosed_radical p) L.toSubgroup w.val at hw
  change SmoothDualClass.HasFixedVector (leviLevel p L.toSubgroup) w.val
  revert hw
  induction w.val using Quotient.inductionOn with
  | h A => exact hcomp L hLK hLN A.obj

/-- Finiteness in one fiber at a normal level from the local predicate for
that Levi alone. -/
theorem finite_semistandardInducedFixedOrbits_of_local
    (K : OpenSubgroup (rationalPoints G))
    (p : SemistandardSpectralIndex i)
    (hcomp : RationalSemistandardNormalLevelFixedComparisonAt.{u, uV} p K)
    (hlocal : (chosenLeviModel p).LocalOrbitFiniteness.{u, uV})
    (L : CompactOpenSubgroup (rationalPoints G)) (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hLN : (L.toSubgroup.subgroupOf K.toSubgroup).Normal) :
    (inducedDiscreteSeriesFixedOrbits (decomposition p) (isClosed_radical p)
      ((chosenLeviModel p).splitCenter (a p))
      ((chosenLeviModel p).splitCenter_le_center (a p) (ha p)) (mu p)
      (chosenLeviModel p).normCharacters L.toSubgroup :
        Set (OrbitClass.{u, uV} (chosenLeviModel p) (a p) (ha p) (mu p))).Finite :=
  (finite_fixedOrbits_of_local (chosenLeviModel p) hlocal (a p) (ha p) (mu p)
    (leviLevel p L.toSubgroup) (isOpen_leviLevel p L.toSubgroup L.1.isOpen)
    (isCompact_leviLevel p L.toSubgroup L.2)).subset
      (inducedFixedOrbits_subset_leviFixed a ha mu K p hcomp L hLK hLN)

/-- Full VIII.1.3(i), retaining geometric index finiteness and the exact
normal-level comparison, from local VIII.1.2 for every semistandard Levi. -/
theorem finite_rationalSemistandardThetaFixed
    (K : OpenSubgroup (rationalPoints G)) (hKc : IsCompact (K : Set (rationalPoints G)))
    (hgeo : Finite (SemistandardSpectralIndex i))
    (hcomp : RationalSemistandardNormalLevelFixedComparison.{u, uV} (i := i) K)
    (hlocal : AllLeviOrbitFiniteness.{u, uV} (i := i))
    (H : Subgroup (rationalPoints G)) (hHo : IsOpen (H : Set (rationalPoints G)))
    (hHc : IsCompact (H : Set (rationalPoints G))) :
    (rationalSemistandardThetaFixed.{u, uV} a ha mu H).Finite := by
  let : Finite (SemistandardSpectralIndex i) := hgeo
  apply finite_of_compactOpenNormalRefinement K (compactOpenNormalRefinement K hKc)
    (rationalSemistandardThetaFixed a ha mu)
    (rationalSemistandardThetaFixed_antitone a ha mu) _ H hHo hHc
  intro L hLK hLN
  exact Set.finite_univ.sigma fun p _ =>
    finite_semistandardInducedFixedOrbits_of_local a ha mu K p (hcomp p)
      (hlocal p (chosenLeviModel p)) L hLK hLN

/-- Proper VIII.1.3(i): only proper Levi predicates occur in the premise. -/
theorem finite_rationalProperSemistandardThetaFixed
    (K : OpenSubgroup (rationalPoints G)) (hKc : IsCompact (K : Set (rationalPoints G)))
    (hgeo : Finite (SemistandardSpectralIndex i))
    (hcomp : RationalProperSemistandardNormalLevelFixedComparison.{u, uV} (i := i) K)
    (hlocal : ProperLeviOrbitFiniteness.{u, uV} (i := i))
    (H : Subgroup (rationalPoints G)) (hHo : IsOpen (H : Set (rationalPoints G)))
    (hHc : IsCompact (H : Set (rationalPoints G))) :
    (rationalSemistandardThetaFixed.{u, uV} a ha mu H ∩
      rationalSemistandardThetaProper.{u, uV} a ha mu).Finite := by
  let : Finite (SemistandardSpectralIndex i) := hgeo
  apply finite_of_compactOpenNormalRefinement K (compactOpenNormalRefinement K hKc)
    (fun L => rationalSemistandardThetaFixed a ha mu L ∩ rationalSemistandardThetaProper a ha mu)
    (fun _ _ h => Set.inter_subset_inter_left _
      (rationalSemistandardThetaFixed_antitone a ha mu h)) _ H hHo hHc
  intro L hLK hLN
  have hfin := (Set.toFinite {p : SemistandardSpectralIndex i | p.IsProper}).sigma
    (fun p hp => finite_semistandardInducedFixedOrbits_of_local a ha mu K p (hcomp p hp)
      (hlocal p hp (chosenLeviModel p)) L hLK hLN)
  apply hfin.subset
  intro t ht
  exact ⟨ht.2, (mem_rationalSemistandardThetaFixed a ha mu L.toSubgroup t).mp ht.1⟩

/-- Exact conditional full VIII.1.3(i) target. This proposition records all
remaining inputs instead of assuming spectral finiteness as structural data. -/
def RationalSemistandardThetaFixedFinitenessStatement
    (K : OpenSubgroup (rationalPoints G)) : Prop :=
  (∀ p, BorelSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))) →
    IsCompact (K : Set (rationalPoints G)) → Finite (SemistandardSpectralIndex i) →
    RationalSemistandardNormalLevelFixedComparison.{u, uV} (i := i) K →
    AllLeviOrbitFiniteness.{u, uV} (i := i) →
    ∀ H : Subgroup (rationalPoints G), IsOpen (H : Set (rationalPoints G)) →
      IsCompact (H : Set (rationalPoints G)) →
      (rationalSemistandardThetaFixed.{u, uV} a ha mu H).Finite

/-- Exact conditional proper VIII.1.3(i) target, with no VIII.1.2 premise for G. -/
def RationalProperSemistandardThetaFixedFinitenessStatement
    (K : OpenSubgroup (rationalPoints G)) : Prop :=
  (∀ p, BorelSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))) →
    IsCompact (K : Set (rationalPoints G)) → Finite (SemistandardSpectralIndex i) →
    RationalProperSemistandardNormalLevelFixedComparison.{u, uV} (i := i) K →
    ProperLeviOrbitFiniteness.{u, uV} (i := i) →
    ∀ H : Subgroup (rationalPoints G), IsOpen (H : Set (rationalPoints G)) →
      IsCompact (H : Set (rationalPoints G)) →
      (rationalSemistandardThetaFixed.{u, uV} a ha mu H ∩
        rationalSemistandardThetaProper.{u, uV} a ha mu).Finite

omit [∀ p, BorelSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))] in
/-- The full conditional target is discharged by the explicit elementary adapter. -/
theorem rationalSemistandardThetaFixedFiniteness
    (K : OpenSubgroup (rationalPoints G)) :
    RationalSemistandardThetaFixedFinitenessStatement.{u, uV} a ha mu K := by
  intro hBorel
  let : ∀ p, BorelSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p)) := hBorel
  exact finite_rationalSemistandardThetaFixed a ha mu K

omit [∀ p, BorelSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))] in
/-- The proper conditional target is discharged without using local finiteness for G. -/
theorem rationalProperSemistandardThetaFixedFiniteness
    (K : OpenSubgroup (rationalPoints G)) :
    RationalProperSemistandardThetaFixedFinitenessStatement.{u, uV} a ha mu K := by
  intro hBorel
  let : ∀ p, BorelSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p)) := hBorel
  exact finite_rationalProperSemistandardThetaFixed a ha mu K

end Families

end Langlands.HarishChandraSchwartz

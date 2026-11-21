import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardInvariantComparison
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardSpectralAction
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardStandardComparison

/-! # Waldspurger's invariant smooth spectral families -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 900000

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz

open RationalSemistandard
open RationalSemistandard.InvariantComparison (Representatives)
open RationalSemistandard.WeylOrbits (conjugateBase weylElement)
open RationalSemistandard.WeylSections (orbitFiber)

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
  {Z : SemistandardSpectralIndex i → CommGroupScheme (Spec (CommRingCat.of F))}
  {a : ∀ p, (Z p).toGrp ⟶ (chosenLeviModel p).scheme}
  {ha : ∀ p, IsSplitComponent (a p)}
  [∀ p, ((chosenLeviModel p).splitCenter (a p)).Normal]
  [∀ p, MeasurableSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))]
  {mu : ∀ p, Measure (levi p ⧸ (chosenLeviModel p).splitCenter (a p))}
  [∀ p, (mu p).IsHaarMeasure]
  {d : ∀ p : SemistandardSpectralIndex i, CompactData p}
  {hG : IsConnectedReductive G}
  (C : WeylSectionComparisonData.{u, uV} a ha mu d hG)

set_option hygiene false in
set_option quotPrecheck false in
local notation "Θ" => RationalSemistandardTheta.{u, uV} a ha mu

namespace RationalSemistandard.WeylSectionComparisonData

/-- Each actual Weyl element and each parabolic with the conjugate Levi
have a comparison arrow lifted to the common source compact. -/
theorem exists_lift (t : Θ) (q : SemistandardSpectralIndex i) (w : relativeWeylGroup i)
    (hw : relativeWeylConjugateSubgroupFunctor i t.1.levi (C.centralizer_le t.1) w = q.levi) :
    ∃ n : C.Lift t q, (weylElement (C.centralizer_le t.1) (d t.1).compact n).val = w := by
  obtain ⟨g, hg, hclass⟩ := C.hasWeylRepresentatives t.1 w
  have hmem : w ∈ semistandardWeylConjugacySet i t.1.toLevi q.toLevi (C.centralizer_le t.1) :=
    hw
  exact ⟨⟨g, hg, hclass.symm ▸ hmem⟩, hclass⟩

variable [∀ p, BorelSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))]

/-- The target lies in the orbit transported by this actual relative Weyl
element, in the component at the specified parabolic. -/
theorem target_transports (t : Θ) (q : SemistandardSpectralIndex i) (n : C.Lift t q) :
    Association.WeylTransports a ha mu
      (weylElement (C.centralizer_le t.1) (d t.1).compact n).val t (C.target t q n) :=
  InvariantComparison.weylTransports_targetIndex a ha mu d t q (C.centralizer_le t.1) n

end RationalSemistandard.WeylSectionComparisonData

variable [∀ p, BorelSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))]

namespace RationalSemistandard

/-- The VI.3 condition on every actual inducing object, at each relative
Weyl arrow lifted to the source compact and every conjugate-Levi parabolic. -/
def IsWeylInvariant (f : RationalSemistandardThetaSections.{u, uV} a ha mu) : Prop :=
  ∀ (t : Θ) (q : SemistandardSpectralIndex i) (n : C.Lift t q)
    (A : Representatives a ha mu t),
    f (C.target t q n) (C.representative t q n A) = C.fiberComparison t q n A (f t A)

/-- The pointwise condition covers the entire relative Weyl group and
exactly those target parabolics whose Levi is the Weyl conjugate. -/
theorem isWeylInvariant_iff (f : RationalSemistandardThetaSections.{u, uV} a ha mu) :
    IsWeylInvariant C f ↔
    ∀ (t : Θ) (w : relativeWeylGroup i) (q : SemistandardSpectralIndex i),
      relativeWeylConjugateSubgroupFunctor i t.1.levi (C.centralizer_le t.1) w = q.levi →
      ∀ (n : C.Lift t q),
        (weylElement (C.centralizer_le t.1) (d t.1).compact n).val = w →
        ∀ A : Representatives a ha mu t,
          f (C.target t q n) (C.representative t q n A) = C.fiberComparison t q n A (f t A) := by
  constructor
  · intro hf t w q hw n hn A
    exact hf t q n A
  · intro hf t q n A
    exact hf t _ q n.property.2 n rfl A

/-- The pointwise comparison intertwines the actions in the two actual
fibers, so invariance is stable under the full product action. -/
theorem IsWeylInvariant.action (x : rationalPoints G × rationalPoints G)
    {f : RationalSemistandardThetaSections.{u, uV} a ha mu} (hf : IsWeylInvariant C f) :
    IsWeylInvariant C (rationalSemistandardThetaRepresentation.{u, uV} a ha mu x f) := by
  intro t q n A
  let T := C.fiberComparison t q n A
  change (orbitFiber (conjugateBase (C.centralizer_le t.1) (d t.1).compact n A.val)).representation
    x (f (C.target t q n) (C.representative t q n A)) =
    T ((orbitFiber A.val).representation x (f t A))
  rw [hf t q n A]
  exact (congrArg (fun L => L (f t A)) (T.isIntertwining' x)).symm

end RationalSemistandard

set_option hygiene false in
set_option quotPrecheck false in
local notation "SmoothFamilies" => rationalSemistandardThetaSmoothSections.{u, uV} a ha mu d

/-- Waldspurger's invariant spectral space inside the actual coherent smooth
finite-support family. This construction uses the certified V.3 comparison. -/
def rationalSemistandardThetaInvariantSections : Submodule ℂ SmoothFamilies where
  carrier := {f | IsWeylInvariant C f.val}
  zero_mem' := by
    intro t q n A
    exact (C.fiberComparison t q n A).map_zero.symm
  add_mem' := by
    intro f g hf hg t q n A
    change f.val (C.target t q n) (C.representative t q n A) +
      g.val (C.target t q n) (C.representative t q n A) =
      C.fiberComparison t q n A (f.val t A + g.val t A)
    rw [hf t q n A, hg t q n A]
    exact ((C.fiberComparison t q n A).map_add _ _).symm
  smul_mem' := by
    intro c f hf t q n A
    change c • f.val (C.target t q n) (C.representative t q n A) =
      C.fiberComparison t q n A (c • f.val t A)
    rw [hf t q n A]
    exact ((C.fiberComparison t q n A).map_smul _ _).symm

@[simp] theorem mem_rationalSemistandardThetaInvariantSections (f : SmoothFamilies) :
    f ∈ rationalSemistandardThetaInvariantSections C ↔ IsWeylInvariant C f.val := Iff.rfl

/-- The invariant family's inclusion into all actual inducing fibers. -/
def rationalSemistandardThetaInvariantInclusion :
    rationalSemistandardThetaInvariantSections C →ₗ[ℂ]
      RationalSemistandardThetaSections.{u, uV} a ha mu :=
  (rationalSemistandardThetaSmoothSections.{u, uV} a ha mu d).subtype.comp
    (rationalSemistandardThetaInvariantSections C).subtype

theorem rationalSemistandardThetaInvariantInclusion_injective :
    Function.Injective (rationalSemistandardThetaInvariantInclusion C) :=
  Subtype.val_injective.comp Subtype.val_injective

/-- The source action on the invariant space is the restriction of the
existing action on the full smooth family. -/
def rationalSemistandardThetaInvariantRepresentation :
    Representation ℂ (rationalPoints G × rationalPoints G)
      (rationalSemistandardThetaInvariantSections C) :=
  (rationalSemistandardThetaSmoothRepresentation.{u, uV} a ha mu d).subrepresentation
    (rationalSemistandardThetaInvariantSections C) (fun x _ hf => IsWeylInvariant.action C x hf)

@[simp] theorem rationalSemistandardThetaInvariantRepresentation_val
    (x : rationalPoints G × rationalPoints G) (f : rationalSemistandardThetaInvariantSections C) :
    (rationalSemistandardThetaInvariantRepresentation C x f).val =
      rationalSemistandardThetaSmoothRepresentation.{u, uV} a ha mu d x f.val := rfl

/-- The inclusion into the full smooth family is an injective intertwiner. -/
def rationalSemistandardThetaInvariantIntertwining :
    (rationalSemistandardThetaInvariantRepresentation C).IntertwiningMap
      (rationalSemistandardThetaSmoothRepresentation.{u, uV} a ha mu d) where
  toLinearMap := (rationalSemistandardThetaInvariantSections C).subtype
  isIntertwining' _ := rfl

/-- The same open subgroup that fixes the underlying smooth family fixes
the invariant vector. -/
theorem rationalSemistandardThetaInvariantRepresentation_isSmooth :
    Langlands.IsSmooth (R := ℂ) (G := rationalPoints G × rationalPoints G)
      (V := rationalSemistandardThetaInvariantSections C)
      (rationalSemistandardThetaInvariantRepresentation C) := by
  intro f
  obtain ⟨H, hH⟩ := rationalSemistandardThetaSmoothRepresentation_isSmooth.{u, uV} a ha mu d f.val
  exact ⟨H, fun x => Subtype.ext (hH x)⟩

/-- The invariant space in the canonical complex smooth category. -/
def rationalSemistandardThetaInvariantObject :=
  @SmoothRep.of ℂ (rationalPoints G × rationalPoints G) _ _ _
    (rationalSemistandardThetaInvariantSections C) _ _
    (rationalSemistandardThetaInvariantRepresentation C)
    (by with_reducible exact rationalSemistandardThetaInvariantRepresentation_isSmooth C)

section StandardRestriction

variable {nu : cocharacterLattice S}
  (hi : IsMaximalSplitTorus i) (hnu : IsGenericCocharacter i nu)
  {B : Finset (RationalPointFamily.SimpleRoot i nu) → CommGroupScheme (Spec (CommRingCat.of F))}
  (b : ∀ I, (B I).toGrp ⟶ (standardLeviModel hG hi hnu I).scheme)
  (hb : ∀ I, IsSplitComponent (b I))
  [∀ I, (rationalLeviSplitCenter I (b I)).Normal]
  [∀ I, MeasurableSpace (levi (standardIndex hG hi hnu I) ⧸ rationalLeviSplitCenter I (b I))]
  [∀ I, BorelSpace (levi (standardIndex hG hi hnu I) ⧸ rationalLeviSplitCenter I (b I))]
  (eta : ∀ I, Measure (levi (standardIndex hG hi hnu I) ⧸ rationalLeviSplitCenter I (b I)))
  [∀ I, (eta I).IsHaarMeasure]
  (hds : RationalSemistandardStandardDiscreteSeriesComparison.{u, uV} a ha mu hG hi hnu b hb eta)
  (hsm : ModelSmoothComparisonStatement.{u, uV} (F := F) (G := G) (i := i))
  {K : OpenSubgroup (rationalPoints G)} (hK : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i nu ∅) (K : Subgroup (rationalPoints G)))

/-- The actual invariant family restricts into the published standard smooth
family by the standard index, model and inducing comparison. -/
def rationalSemistandardThetaInvariantStandardRestrict :
    rationalSemistandardThetaInvariantSections C →ₗ[ℂ]
      rationalStandardThetaSmoothSections.{u, uV} hG hi hnu hK hPK b hb eta :=
  (rationalStandardFullSmoothRestrict.{u, uV} a ha mu hG hi hnu b hb eta hds d hsm hK hPK).comp
    (rationalSemistandardThetaInvariantSections C).subtype

@[simp] theorem rationalSemistandardThetaInvariantStandardRestrict_apply
    (f : rationalSemistandardThetaInvariantSections C) :
    rationalSemistandardThetaInvariantStandardRestrict C hi hnu b hb eta hds hsm hK hPK f =
      rationalStandardFullSmoothRestrict.{u, uV} a ha mu hG hi hnu b hb eta hds d hsm hK hPK f.val :=
  rfl

end StandardRestriction

end Langlands.HarishChandraSchwartz

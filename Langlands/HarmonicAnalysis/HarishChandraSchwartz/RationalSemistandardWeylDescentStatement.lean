import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardWeylSectionStatement
import Langlands.Representation.Plancherel.ProductInducedOrbitBaseChange

/-! # Descent of the actual semistandard normalized comparisons -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 750000
set_option backward.isDefEq.respectTransparency.types true

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel Langlands.Induction

namespace Langlands.HarishChandraSchwartz.RationalSemistandard.WeylDescent

open WeylOrbits WeylComparison WeylSections
open ActualConjugateLeviCoherence (LeviNormalization TransportedValue)
open DynamicOppositeStandardIntertwining (levi_isClosed)
open Langlands.BruhatTits.SpecialCompact (HasWeylRepresentatives)

attribute [local instance]
  rationalWeightsIsAffine rationalWeightsTopology rationalWeightsTopologicalGroup
  rationalWeightsT2Field rationalWeightsLocallyCompact rationalWeightsMeasurableSpace
  rationalWeightsBorelSpace rationalInducedSecondCountable rationalInducedT2
  rationalInducedNonarchimedean
  DynamicOppositeStandardIntertwining.centralizerClosedImmersion
  DynamicOppositeStandardIntertwining.centralizerAffine
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace2
  LeviNormalization.normal LeviNormalization.quotientMeasurable LeviNormalization.quotientBorel
  LeviNormalization.quotientHaar LeviNormalization.quotientInversion

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] {i : S.toGrp ⟶ G}

local instance parabolicLocallyCompact (p : SemistandardSpectralIndex i) :
    LocallyCompactSpace (parabolic p) := (isClosed_parabolic p).locallyCompactSpace
local instance dynamicLeviLocallyCompact (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) :
    LocallyCompactSpace (DynamicOppositeStandardIntertwining.levi χ) :=
  (levi_isClosed χ).locallyCompactSpace

section Recenter

variable {p : SemistandardSpectralIndex i} (m : LeviModel p) (d : CompactData p)
  (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p))

set_option hygiene false in
local notation "Ω" => UnitaryOrbitRepresentative m.normCharacters π

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
private theorem twistClass_eq_self
    {a : levi p →* ℂˣ} (ha : IsOpen (a.ker : Set (levi p))) (ha₁ : a = 1)
    (C : SmoothDualClass.{0, u, uV} (k := ℂ) (G := levi p)) :
    SmoothDualClass.twist a ha C = C := by
  subst a
  exact SmoothDualClass.twist_one ha C

private def baseMember : Ω :=
  ⟨π, 1, by
    apply twistClass_eq_self _ ?_
    rw [map_one]
    rfl⟩

/-- An isomorphism of actual inducing representations preserves orbit membership. -/
abbrev memberOfIso (A : Ω) (B : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p))
    (e : A.val.obj ≅ B.obj) : Ω := by
  refine ⟨B, ?_⟩
  obtain ⟨z, hz⟩ := A.property
  exact ⟨z, hz.trans (Quotient.sound ⟨IrreducibleAdmissibleRep.isoMk e⟩)⟩

/-- The canonical smooth-section comparison when the base is replaced by
any actual representative in the orbit. -/
def recenterSections (A : Ω) : smoothOrbitSections m d π ≃ₗ[ℂ] smoothOrbitSections m d A.val :=
  productInducedSmoothOrbitBaseEquiv m.normCharacters π A (decomposition p) (isClosed_radical p)
    m.unitaryCoordinates.toMulEquiv d.compact (isClosed_parabolic p) d.isCompact
    m.continuous_normCharacters d.projection_continuous d.factorization

end Recenter

section WeylQuotient

variable {p q : SemistandardSpectralIndex i}
  (m : LeviModel p) (m' : LeviModel q) (d : CompactData p) (d' : CompactData q)
  (hP : torusCentralizer i ≤ p.levi) (hQ : torusCentralizer i ≤ q.levi)
  (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p))

set_option hygiene false in
local notation "K" => d.compact
set_option hygiene false in
local notation "Lift" => CompactLift (p := p) (q := q) hP K
set_option hygiene false in
local notation "WQ" => SemistandardWeylConjugacyQuotient i p.toLevi q.toLevi hP
set_option hygiene false in
local notation "Ω" => UnitaryOrbitRepresentative m.normCharacters π

/-- Class of a compact lift in the published left target-Levi Weyl quotient. -/
def liftClass (n : Lift) : WQ :=
  Quotient.mk (semistandardWeylConjugacyRel i p.toLevi q.toLevi hP) (weylElement hP K n)

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
/-- Exactly the left target-Weyl equivalence relation. -/
theorem liftClass_eq_iff (n n' : Lift) :
    liftClass d hP n = liftClass d hP n' ↔
      (weylElement hP K n').val * (weylElement hP K n).val⁻¹ ∈
        semistandardLeviRelativeWeylSubgroup i q.toLevi :=
  semistandardWeylConjugacyQuotient_mk_eq_iff i p.toLevi q.toLevi hP _ _

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
/-- The source compact's actual Weyl representatives lift every class of
the left target-Levi quotient. -/
theorem liftClass_surjective (hw : HasWeylRepresentatives i (K).toSubgroup) :
    Function.Surjective (liftClass (q := q) d hP) := by
  intro w
  induction w using Quotient.inductionOn with
  | h w =>
    obtain ⟨n, hn, hclass⟩ := hw w.val
    let N : Lift := ⟨n, hn, hclass.symm ▸ w.property⟩
    exact ⟨N, congrArg (Quotient.mk _) (Subtype.ext hclass)⟩

/-- Canonical coefficient transport from the n' target to the n target
when those lifts represent the same actual quotient element. -/
def changeLiftFiber (n n' : Lift) (h : liftClass d hP n = liftClass d hP n')
    (A : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p)) :=
  productInducedCoefficientTransport (decomposition q) (isClosed_radical q)
    (SmoothRep.equivOfIso
      (changeLiftInducingIso hP K n n' hQ ((liftClass_eq_iff d hP n n').mp h) A.obj))

/-- Recenter in the same actual target orbit using the class of the
conjugate inducing object. -/
def recenterTarget (n n' : Lift) (h : liftClass d hP n = liftClass d hP n') :
    smoothOrbitSections m' d' (conjugateBase hP K n π) ≃ₗ[ℂ]
      smoothOrbitSections m' d' (conjugateBase hP K n' π) :=
  recenterSections m' d' (conjugateBase hP K n π)
    (memberOfIso m' (conjugateBase hP K n π) (baseMember m' (conjugateBase hP K n π))
      (conjugateBase hP K n' π)
      (changeLiftInducingIso hP K n n' hQ ((liftClass_eq_iff d hP n n').mp h) π.obj).symm)

variable {hG : IsConnectedReductive G} (r : CocharacterPresentation hG p)
  (r' : CocharacterPresentation hG q) (hK : d'.compact = d.compact)
  (D : LeviNormalization r.hom (dynamicInducing r π.obj))

set_option hygiene false in
local notation "Family" n:max => ComparisonFamily m d hP n π
set_option hygiene false in
local notation "Actual" n:max T:max => IsActualFamily m d d' hP n π r r' hK D T
set_option hygiene false in
local notation "SmoothPair" n:max => (smoothOrbitSections m d π ≃ₗ[ℂ]
  smoothOrbitSections m' d' (conjugateBase hP K n π))

/-- The actual normalized comparison is unchanged after canonical
transport for all lifts in the same quotient class. -/
def LiftFiberIndependence : Prop :=
  ∀ (n n' : Lift) (h : liftClass d hP n = liftClass d hP n')
    (T : Family n) (T' : Family n'),
    Actual n T → Actual n' T' → ∀ (A : Ω) (v : orbitFiber A.val),
      TransportedValue (changeLiftFiber d hP hQ n n' h A.val) (T' A v) (T A v)

/-- With any compatible compact lifts for the quotient, the smooth
comparison is indexed by the actual quotient classes and compatible
with all other lifts after their canonical target recenterings. -/
def QuotientRealization
    (lift : ∀ w : WQ, {n : Lift // liftClass d hP n = w}) : Prop :=
  ∃ L : ∀ w : WQ, SmoothPair ((lift w).val),
    (∀ w : WQ, RespectsLevels m m' d d' hP (lift w).val π (L w) ∧
      ∃ T : Family (lift w).val, Actual (lift w).val T ∧
        Realizes m m' d d' hP (lift w).val π T (L w)) ∧
    ∀ (w : WQ) (n : Lift) (h : liftClass d hP n = w)
      (T : Family n) (U : SmoothPair n),
      Actual n T → Realizes m m' d d' hP n π T U →
      ∀ v : smoothOrbitSections m d π,
        recenterTarget m' d d' hP hQ π n (lift w).val (h.trans (lift w).property.symm) (U v) = L w v

/-- Changing the base of the source twist orbit commutes with the actual
normalized comparison and the associated change of target base. -/
def SourceBaseIndependence : Prop :=
  ∀ (n : Lift) (A : Ω)
    (hA : IsSquareIntegrableModCentralSubgroup D.center D.central
      (dynamicInducing r A.val.obj).representation D.quotientMeasure)
    (hi : (dynamicInducing r A.val.obj).representation.IsIrreducible)
    (T : Family n) (T' : ComparisonFamily m d hP n A.val)
    (L : SmoothPair n)
    (L' : smoothOrbitSections m d A.val ≃ₗ[ℂ]
      smoothOrbitSections m' d' (conjugateBase hP K n A.val)),
    Actual n T → IsActualFamily m d d' hP n A.val r r' hK
      (normalizationAt D _ hA hi) T' →
    Realizes m m' d d' hP n π T L → Realizes m m' d d' hP n A.val T' L' →
    ∀ v : smoothOrbitSections m d π,
      HEq (recenterSections m' d' (conjugateBase hP K n π)
        (conjugateRepresentative hP K n m m' π A) (L v)) (L' (recenterSections m d π A v))

/-- Closed Weyl and orbit descent target with the source's actual
left quotient and the existing coherent smooth sections. -/
def ClosedWeylDescentStatement : Prop :=
  HasIntrinsicSourceNormalization d π r D →
  (∀ n : Lift, ClosedSectionComparisonStatement m m' d d' hP n π r r' hK D) ∧
  LiftFiberIndependence m d d' hP hQ π r r' hK D ∧
  SourceBaseIndependence m m' d d' hP π r r' hK D ∧
  ∀ lift : ∀ w : WQ, {n : Lift // liftClass d hP n = w},
    QuotientRealization m m' d d' hP hQ π r r' hK D lift

end WeylQuotient

section Inner

variable {p : SemistandardSpectralIndex i} (m : LeviModel p) (d : CompactData p)
  (hP : torusCentralizer i ≤ p.levi)
  (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p))
  (n : CompactLift (p := p) (q := p) hP d.compact)
  (hn : (weylElement hP d.compact n).val ∈ semistandardLeviRelativeWeylSubgroup i p.toLevi)

set_option hygiene false in
local notation "Ω" => UnitaryOrbitRepresentative m.normCharacters π

/-- The actual inner conjugation isomorphism for a Weyl lift in the Levi. -/
def innerIso (A : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := levi p)) :
    (conjugateBase hP d.compact n A).obj ≅ A.obj :=
  let x : levi p :=
    ⟨n.val, (mk_mem_semistandardLeviRelativeWeylSubgroup_iff i p.toLevi hP n.val).mp hn⟩
  conjugationFunctorInnerIso x A.obj

/-- The inner-conjugate representative in the same actual orbit. -/
abbrev innerRepresentative (A : Ω) : Ω :=
  memberOfIso m π A (conjugateBase hP d.compact n A.val) (innerIso d hP n hn A.val).symm

/-- The exact intrinsic map specified by inner inducing transport. -/
def innerFiberTransport (A : Ω) :=
  productInducedCoefficientTransport (decomposition p) (isClosed_radical p)
    (SmoothRep.equivOfIso (innerIso d hP n hn A.val).symm)

/-- Coherence of the actual section supplies the automatic covariance for
the inner inducing transport. -/
theorem automaticInnerCovariance (v : smoothOrbitSections m d π) (A : Ω) :
    v.val (innerRepresentative m d hP π n hn A) =
      innerFiberTransport m d hP π n hn A (v.val A) :=
  v.property.1 A (innerRepresentative m d hP π n hn A)
    (SmoothRep.equivOfIso (innerIso d hP n hn A.val).symm)

variable {hG : IsConnectedReductive G} (r : CocharacterPresentation hG p)
  (D : LeviNormalization r.hom (dynamicInducing r π.obj))

/-- VI.3 for the same parabolic and a Weyl lift in the Levi. The actual
normalized comparison equals canonical inner transport at all vectors. -/
def ClosedInnerCovarianceStatement : Prop :=
  HasIntrinsicSourceNormalization d π r D →
  ClosedSectionComparisonStatement m m d d hP n π r r rfl D ∧
    ∀ T : ComparisonFamily m d hP n π,
      IsActualFamily m d d hP n π r r rfl D T →
      ∀ (A : Ω) (v : orbitFiber A.val), T A v = innerFiberTransport m d hP π n hn A v

/-- Once the actual normalized map is identified with inner transport,
the invariant-family equation for this Weyl lift follows from coherence. -/
theorem normalizedInnerCovariance
    (hinner : ClosedInnerCovarianceStatement m d hP π n hn r D)
    (T : ComparisonFamily m d hP n π) (hT : IsActualFamily m d d hP n π r r rfl D T)
    (v : smoothOrbitSections m d π) (A : Ω) :
    v.val (innerRepresentative m d hP π n hn A) = T A (v.val A) :=
  (automaticInnerCovariance m d hP π n hn v A).trans ((hinner hT.1).2 T hT A (v.val A)).symm

end Inner

end Langlands.HarishChandraSchwartz.RationalSemistandard.WeylDescent

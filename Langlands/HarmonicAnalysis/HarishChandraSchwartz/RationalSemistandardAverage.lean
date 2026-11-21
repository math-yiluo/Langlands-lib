import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardInvariance
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSemistandardAssociationCount

/-! # Waldspurger's source average on semistandard spectral families -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz.RationalSemistandard.Average

open InvariantComparison (Representatives)
open WeylOrbits (weylElement)
open WeylSections (orbitFiber)
open Association (WeylParabolicPair)

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
  (hi : IsMaximalSplitTorus i)
  (hD : SemistandardSpectralDynamicCoverageStatement.{u})
  (hfin : SemistandardSpectralFiberFinitenessStatement.{u})

set_option hygiene false in
set_option quotPrecheck false in
local notation "Θ" => RationalSemistandardTheta.{u, uV} a ha mu
set_option hygiene false in
set_option quotPrecheck false in
local notation "Families" => RationalSemistandardThetaSections.{u, uV} a ha mu
set_option hygiene false in
set_option quotPrecheck false in
local notation "SmoothFamilies" => rationalSemistandardThetaSmoothSections.{u, uV} a ha mu d
set_option hygiene false in
set_option quotPrecheck false in
local notation "Component" => rationalSemistandardThetaComponent.{u, uV} a ha mu d

/-- The actual double-sum index for `(O,P)` is all pairs of a relative Weyl
element and a parabolic with the transported Levi. -/
abbrev Pair (t : Θ) :=
  WeylParabolicPair hG hi hD t.1.toLevi (C.centralizer_le t.1)

/-- Enumerate every actual pair using the geometric finiteness theorem. -/
def pairs (t : Θ) : Finset (Pair C hi hD t) :=
  @Finset.univ _ (@Fintype.ofFinite _ (Association.finite_weylParabolicPair hG hi hD hfin
    t.1.toLevi (C.centralizer_le t.1)))

/-- The reciprocal cardinality in VI.3, embedded as a complex scalar. -/
def scale (t : Θ) : ℂ :=
  ((Nat.card (relativeWeylGroup i) : ℂ) *
    (Nat.card (SemistandardSpectralParabolicFiber i t.1.toLevi) : ℂ))⁻¹

theorem pairs_card (t : Θ) :
    (pairs C hi hD hfin t).card =
      Nat.card (relativeWeylGroup i) * Nat.card (SemistandardSpectralParabolicFiber i t.1.toLevi) := by
  let := Association.finite_weylParabolicPair hG hi hD hfin t.1.toLevi (C.centralizer_le t.1)
  let := Fintype.ofFinite (Pair C hi hD t)
  rw [pairs, Finset.card_univ, ← Nat.card_eq_fintype_card]
  exact Association.card_weylParabolicPair hG hi hD t.1.toLevi (C.centralizer_le t.1)

theorem pairs_card_pos (t : Θ) : 0 < (pairs C hi hD hfin t).card := by
  rw [pairs_card]
  let := hG.finite_relativeWeylGroup i hi
  let := (hfin F G hG S i hi t.1.toLevi).1
  let := (hfin F G hG S i hi t.1.toLevi).2
  exact Nat.mul_pos Nat.card_pos Nat.card_pos

theorem scale_mul_card (t : Θ) : scale t * ((pairs C hi hD hfin t).card : ℂ) = 1 := by
  have h : ((pairs C hi hD hfin t).card : ℂ) ≠ 0 := by
    exact_mod_cast (pairs_card_pos C hi hD hfin t).ne'
  rw [pairs_card, Nat.cast_mul] at h
  rw [scale, pairs_card, Nat.cast_mul, inv_mul_cancel₀ h]

/-- Choose a compact lift of the actual Weyl element in one summand.
The choice comparison uses inducing covariance and V.3 descent. -/
def lift (t : Θ) (x : Pair C hi hD t) : C.Lift t x.2.val :=
  (C.exists_lift t x.2.val x.1 x.2.property.symm).choose

theorem lift_weylElement (t : Θ) (x : Pair C hi hD t) :
    (weylElement (C.centralizer_le t.1) (d t.1).compact (lift C hi hD t x)).val = x.1 :=
  (C.exists_lift t x.2.val x.1 x.2.property.symm).choose_spec

set_option hygiene false in
local notation "n" => lift C hi hD t x

variable [∀ p, BorelSpace (levi p ⧸ (chosenLeviModel p).splitCenter (a p))]

theorem target_eq_weylParabolicTarget (t : Θ) (x : Pair C hi hD t) :
    C.target t x.2.val n =
      Association.weylParabolicTarget hG hi hD a ha mu t (C.centralizer_le t.1) x := by
  have hn := C.target_transports t x.2.val n
  rw [lift_weylElement] at hn
  exact hn.eq_of_same_parabolic
    (Association.weylParabolicTarget_transports hG hi hD a ha mu t (C.centralizer_le t.1) x)
    (C.centralizer_le t.1)
    (Association.weylParabolicTarget_parabolic hG hi hD a ha mu t (C.centralizer_le t.1) x).symm

/-- Evaluation of one summand is the inverse of the specified normalized
comparison applied to the actual target coefficient. -/
def summand (t : Θ) (x : Pair C hi hD t) :
    Families →ₗ[ℂ] RationalSemistandardThetaSection.{u, uV} a ha mu t :=
  LinearMap.pi fun A =>
    let T := (C.fiberComparisonEquiv t x.2.val n A).symm
    let B := C.representative t x.2.val n A
    let q := C.target t x.2.val n
    { toFun := fun f => T (f q B)
      map_add' := fun f g => T.map_add (f q B) (g q B)
      map_smul' := fun c f => T.map_smul c (f q B) }

theorem summand_apply (t : Θ) (x : Pair C hi hD t) (f : Families)
    (A : Representatives a ha mu t) :
    summand C hi hD t x f A =
      (C.fiberComparisonEquiv t x.2.val n A).symm
        (f (C.target t x.2.val n) (C.representative t x.2.val n A)) := rfl

/-- The VI.3 average on the full product of actual coefficient fibers. -/
def rawAverage : Families →ₗ[ℂ] Families :=
  LinearMap.pi fun t => scale t • ∑ x ∈ pairs C hi hD hfin t, summand C hi hD t x

theorem rawAverage_apply (f : Families) (t : Θ) (A : Representatives a ha mu t) :
    rawAverage C hi hD hfin f t A =
      scale t • ∑ x ∈ pairs C hi hD hfin t,
        (C.fiberComparisonEquiv t x.2.val n A).symm
          (f (C.target t x.2.val n) (C.representative t x.2.val n A)) := by
  simp only [rawAverage, LinearMap.pi_apply, LinearMap.smul_apply, Pi.smul_apply,
    LinearMap.sum_apply, Finset.sum_apply, summand_apply]

/-- On invariant inputs, each inverse comparison returns the source value
and the reciprocal count cancels the sum of these identical values. -/
theorem rawAverage_eq_self {f : Families} (hf : IsWeylInvariant C f) :
    rawAverage C hi hD hfin f = f := by
  funext t A
  rw [rawAverage_apply]
  have h (x : Pair C hi hD t) :
      (C.fiberComparisonEquiv t x.2.val n A).symm
        (f (C.target t x.2.val n) (C.representative t x.2.val n A)) = f t A :=
    (congrArg (C.fiberComparisonEquiv t x.2.val n A).symm (hf t x.2.val n A)).trans
      ((C.fiberComparisonEquiv t x.2.val n A).symm_apply_apply (f t A))
  simp only [h, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, scale_mul_card, one_smul]

/-- The full product action commutes with each inverse comparison,
and hence with the pointwise average. -/
theorem rawAverage_action (g : rationalPoints G × rationalPoints G) (f : Families) :
    rawAverage C hi hD hfin (rationalSemistandardThetaRepresentation a ha mu g f) =
      rationalSemistandardThetaRepresentation a ha mu g (rawAverage C hi hD hfin f) := by
  funext t A
  let T := (orbitFiber A.val).representation g
  change rawAverage C hi hD hfin (rationalSemistandardThetaRepresentation a ha mu g f) t A =
    T (rawAverage C hi hD hfin f t A)
  rw [rawAverage_apply, rawAverage_apply, map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  exact congrArg (fun L => L (f (C.target t x.2.val n) (C.representative t x.2.val n A)))
    ((C.fiberComparisonEquiv t x.2.val n A).symm.isIntertwining' g)

/-- The same sum of inverse comparisons in the actual smooth component. -/
def smoothComponent (f : SmoothFamilies) (t : Θ) :
    rationalSemistandardThetaComponentSpace.{u, uV} a ha mu d t :=
  scale t • ∑ x ∈ pairs C hi hD hfin t,
    (C.smoothComparison t x.2.val n).symm (Component (C.target t x.2.val n) f)

theorem smoothComponent_val (f : SmoothFamilies) (t : Θ) :
    (smoothComponent C hi hD hfin f t).val = rawAverage C hi hD hfin f.val t := by
  funext A
  let ev : rationalSemistandardThetaComponentSpace.{u, uV} a ha mu d t →ₗ[ℂ]
      orbitFiber A.val :=
    (LinearMap.proj A).comp (rationalSemistandardThetaComponentSpace a ha mu d t).subtype
  change ev (smoothComponent C hi hD hfin f t) = _
  rw [smoothComponent, map_smul, map_sum, rawAverage_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  exact C.smoothComparison_symm_apply t x.2.val n (Component (C.target t x.2.val n) f) A

/-- The output can be supported only in classes meeting the input support. -/
theorem support_rawAverage_subset (f : Families) :
    rationalSemistandardThetaSupport a ha mu (rawAverage C hi hD hfin f) ⊆
      Association.associationSaturation a ha mu (rationalSemistandardThetaSupport a ha mu f) := by
  classical
  intro t ht
  by_contra h
  apply ht
  funext A
  rw [rawAverage_apply]
  change _ = 0
  have hz (x : Pair C hi hD t) : f (C.target t x.2.val n) = 0 := by
    by_contra hx
    apply h
    exact (Association.mem_associationSaturation a ha mu _ t).mpr
      ⟨_, hx, ⟨_, (C.target_transports t x.2.val n).inv⟩⟩
  apply smul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro x hx
  have hv : f (C.target t x.2.val n) (C.representative t x.2.val n A) = 0 :=
    congrFun (hz x) (C.representative t x.2.val n A)
  exact (congrArg (C.fiberComparisonEquiv t x.2.val n A).symm hv).trans
    (map_zero (C.fiberComparisonEquiv t x.2.val n A).symm)

theorem finite_support_rawAverage (f : SmoothFamilies) :
    (rationalSemistandardThetaSupport a ha mu (rawAverage C hi hD hfin f.val)).Finite := by
  apply Set.Finite.subset _ (support_rawAverage_subset C hi hD hfin f.val)
  exact f.property.2.biUnion fun t _ =>
    Association.finite_associatedIndices a ha mu hG hi hfin t (C.centralizer_le t.1)

/-- The particular pointwise average has coherent smooth components and finite
support, by the closed V.3 section comparison and geometric finiteness. -/
theorem rawAverage_mem_smooth (f : SmoothFamilies) :
    rawAverage C hi hD hfin f.val ∈ SmoothFamilies :=
  ⟨fun t => (smoothComponent_val C hi hD hfin f t) ▸ (smoothComponent C hi hD hfin f t).property,
    finite_support_rawAverage C hi hD hfin f⟩

/-- The actual average, with the smooth finite-support codomain. -/
def smoothAverage : SmoothFamilies →ₗ[ℂ] SmoothFamilies :=
  ((rawAverage C hi hD hfin).comp (SmoothFamilies).subtype).codRestrict
    SmoothFamilies (rawAverage_mem_smooth C hi hD hfin)

@[simp] theorem smoothAverage_val (f : SmoothFamilies) :
    (smoothAverage C hi hD hfin f).val = rawAverage C hi hD hfin f.val := rfl

theorem smoothAverage_eq_self {f : SmoothFamilies}
    (hf : f ∈ rationalSemistandardThetaInvariantSections C) :
    smoothAverage C hi hD hfin f = f :=
  Subtype.ext (rawAverage_eq_self C hi hD hfin hf)

theorem smoothAverage_action (g : rationalPoints G × rationalPoints G) (f : SmoothFamilies) :
    smoothAverage C hi hD hfin (rationalSemistandardThetaSmoothRepresentation a ha mu d g f) =
      rationalSemistandardThetaSmoothRepresentation a ha mu d g (smoothAverage C hi hD hfin f) :=
  Subtype.ext (rawAverage_action C hi hD hfin g f.val)

/-- On coherent smooth inputs, another compact lift of the same Weyl
element gives the same inverse-comparison summand in the source fiber. -/
def LiftIndependenceStatement : Prop :=
  ∀ (t : Θ) (x : Pair C hi hD t) (n' : C.Lift t x.2.val),
    (weylElement (C.centralizer_le t.1) (d t.1).compact n').val = x.1 →
    ∀ (f : SmoothFamilies) (A : Representatives a ha mu t),
      (C.fiberComparisonEquiv t x.2.val n' A).symm
        (f.val (C.target t x.2.val n') (C.representative t x.2.val n' A)) =
      summand C hi hD t x f.val A

/-- VI.3 invariant image for the particular inverse-comparison sum.
Each output satisfies the pointwise condition at every actual Weyl arrow. -/
def InvariantImageStatement : Prop :=
  ∀ f : SmoothFamilies, IsWeylInvariant C (rawAverage C hi hD hfin f.val)

/-- Waldspurger's projector with its actual invariant codomain, conditional
on the invariant image of the specified average. -/
def invariantProjector (h : InvariantImageStatement C hi hD hfin) :
    SmoothFamilies →ₗ[ℂ] rationalSemistandardThetaInvariantSections C :=
  (smoothAverage C hi hD hfin).codRestrict (rationalSemistandardThetaInvariantSections C) h

@[simp] theorem invariantProjector_val (h : InvariantImageStatement C hi hD hfin)
    (f : SmoothFamilies) :
    (invariantProjector C hi hD hfin h f).val = smoothAverage C hi hD hfin f := rfl

theorem invariantProjector_apply (h : InvariantImageStatement C hi hD hfin)
    (f : SmoothFamilies) (t : Θ) (A : Representatives a ha mu t) :
    (invariantProjector C hi hD hfin h f).val.val t A =
      scale t • ∑ x ∈ pairs C hi hD hfin t,
        (C.fiberComparisonEquiv t x.2.val n A).symm
          (f.val (C.target t x.2.val n) (C.representative t x.2.val n A)) :=
  rawAverage_apply C hi hD hfin f.val t A

theorem invariantProjector_retract (h : InvariantImageStatement C hi hD hfin)
    (f : rationalSemistandardThetaInvariantSections C) :
    invariantProjector C hi hD hfin h f.val = f :=
  Subtype.ext (smoothAverage_eq_self C hi hD hfin f.property)

theorem smoothAverage_idempotent (h : InvariantImageStatement C hi hD hfin) :
    (smoothAverage C hi hD hfin).comp (smoothAverage C hi hD hfin) =
      smoothAverage C hi hD hfin :=
  LinearMap.ext fun f => smoothAverage_eq_self C hi hD hfin (h f)

theorem smoothAverage_range (h : InvariantImageStatement C hi hD hfin) :
    LinearMap.range (smoothAverage C hi hD hfin) = rationalSemistandardThetaInvariantSections C := by
  ext f
  constructor
  · rintro ⟨v, rfl⟩
    exact h v
  · intro hf
    exact ⟨f, smoothAverage_eq_self C hi hD hfin hf⟩

theorem invariantProjector_action (h : InvariantImageStatement C hi hD hfin)
    (g : rationalPoints G × rationalPoints G) (f : SmoothFamilies) :
    invariantProjector C hi hD hfin h (rationalSemistandardThetaSmoothRepresentation a ha mu d g f) =
      rationalSemistandardThetaInvariantRepresentation C g (invariantProjector C hi hD hfin h f) :=
  Subtype.ext (smoothAverage_action C hi hD hfin g f)

end Langlands.HarishChandraSchwartz.RationalSemistandard.Average

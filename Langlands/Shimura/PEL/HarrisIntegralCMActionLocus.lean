import Langlands.Shimura.PEL.HarrisIntegralCMEquationLocus
import Langlands.Shimura.PEL.HarrisIntegralRosatiComparison
import Langlands.Shimura.PEL.HarrisIntegralActionDeterminantLocus
import Langlands.AbelianScheme.RelativeDualBaseChangeCoherence
import Langlands.AbelianScheme.PolarizedFiniteLevel.Pullback

/-! # The joint Rosati and determinant locus of actual integral Harris actions -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Module Opposite
open Langlands.AbelianScheme Langlands.GroupScheme.Cartier
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AbelianScheme.PolarizedFiniteLevel

namespace Langlands.Shimura.PEL.HarrisPolarizedWeilLevel

open NumberField _root_.Algebra

variable {E F A : Type}
    [Field E] [NumberField E] [IsTotallyReal E]
    [Field F] [NumberField F] [IsTotallyComplex F]
    [Algebra E F] [IsQuadraticExtension E F]
    [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
    [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ F A]
    {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
    {L : Type} [Field L] [NumberField L] [IsCMField L]
    [IsQuadraticExtension ℚ L] [Algebra L F]
    {τ₀ : L →+* ℂ}
    (C : HarrisSignatureCharts D.toSecondKindInvolution n
      (harrisCMSection E (algebraMap L F) τ₀))
    (P : Prerequisites.{0})
    {S : Scheme.{0}} (p : S ⟶ Spec (.of F))
    (B : Langlands.AbelianScheme S) (W : DualWitness B)
    (lam : B ⟶ W.dual P)

local notation "O" => D.harrisHodgePELIntegralOrder C
local notation "basisO" => D.harrisHodgePELIntegralBasis C

/-- The actual basis Rosati condition for canonical direct pullback of a fixed map. -/
def harrisIntegralActionRosatiCondition (T : Over S)
    (a : O →+* CategoryTheory.End ((baseChange T.hom).obj B)) : Prop :=
  IntegralRosatiBasisEquations D C P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability ((baseChange T.hom).obj B)
    (W.pullback P T.hom).hasDual (W.pullback P T.hom).inverseBundle
    (W.pullback P T.hom).evaluation (W.pullback P T.hom).geometry a
    (W.pullbackMap P T.hom (W.pullback P T.hom) lam)

omit [IsScalarTower ℚ F A] in
/-- The direct-family Rosati condition is precisely the successive pullback condition. -/
theorem harrisIntegralActionRosati_restrict_iff
    {T T' : Over S} (f : T' ⟶ T)
    (a : O →+* CategoryTheory.End ((baseChange T.hom).obj B)) :
    harrisIntegralActionRosatiCondition D C P B W lam T'
        ((relativeEndRestrict B f).comp a) ↔
      IntegralRosatiBasisEquations D C P.preservation P.composition P.unitCoherence
        P.associativity P.comparison P.symmetry P.stability
        ((baseChange f.left).obj ((baseChange T.hom).obj B))
        ((W.pullback P T.hom).pullback P f.left).hasDual
        ((W.pullback P T.hom).pullback P f.left).inverseBundle
        ((W.pullback P T.hom).pullback P f.left).evaluation
        ((W.pullback P T.hom).pullback P f.left).geometry
        (baseChangeOrderAction f.left ((baseChange T.hom).obj B) a)
        ((W.pullback P T.hom).pullbackMap P f.left
          ((W.pullback P T.hom).pullback P f.left)
          (W.pullbackMap P T.hom (W.pullback P T.hom) lam)) := by
  let WT := W.pullback P T.hom
  let WD := W.pullback P T'.hom
  let WC := WT.pullback P f.left
  have hc :
      relativeIntegralRosatiComparisonMap P.preservation P.composition P.unitCoherence
        P.associativity P.comparison P.symmetry P.stability B f
        WC.hasDual WC.inverseBundle WC.evaluation WC.geometry
        WD.hasDual WD.inverseBundle WD.evaluation WD.geometry
        (WT.pullbackMap P f.left WC (W.pullbackMap P T.hom WT lam)) =
      W.pullbackMap P T'.hom WD lam := by
    simpa only [relativeIntegralRosatiComparisonMap, integralRosatiComparisonMap,
      DualWitness.pullbackMap, DualWitness.baseChangeIso, dualAbelianBaseChangeMap,
      Category.assoc] using
      (dualAbelianBaseChangeMap_relative_comp_pullback P.preservation P.stability
        P.composition P.unitCoherence P.associativity P.comparison P.symmetry
        P.universality P.compatibility B W.hasDual W.geometry W.inverseBundle W.evaluation
        f WT.hasDual WT.geometry WT.inverseBundle WT.evaluation
        WD.hasDual WD.geometry WD.inverseBundle WD.evaluation
        WC.hasDual WC.geometry WC.inverseBundle WC.evaluation lam)
  have h := integralRosatiBasisEquations_relativeComparison_iff D C P.preservation
    P.composition P.unitCoherence P.associativity P.comparison P.symmetry P.stability B f
    WC.hasDual WC.inverseBundle WC.evaluation WC.geometry
    WD.hasDual WD.inverseBundle WD.evaluation WD.geometry a
    (WT.pullbackMap P f.left WC (W.pullbackMap P T.hom WT lam))
  rw [hc] at h
  exact h

omit [IsScalarTower ℚ F A] in
/-- Canonical relative action restriction preserves Rosati for the original fixed map. -/
theorem harrisIntegralActionRosati_restrict
    {T T' : Over S} (f : T' ⟶ T)
    (a : O →+* CategoryTheory.End ((baseChange T.hom).obj B))
    (ha : harrisIntegralActionRosatiCondition D C P B W lam T a) :
    harrisIntegralActionRosatiCondition D C P B W lam T'
      ((relativeEndRestrict B f).comp a) := by
  apply (harrisIntegralActionRosati_restrict_iff D C P B W lam f a).mpr
  exact IntegralRosatiBasisEquations.baseChange D C P.preservation P.composition
    P.unitCoherence P.associativity P.comparison P.symmetry P.stability
    P.universality P.compatibility f.left ((baseChange T.hom).obj B)
    (W.pullback P T.hom).hasDual (W.pullback P T.hom).inverseBundle
    (W.pullback P T.hom).evaluation (W.pullback P T.hom).geometry
    ((W.pullback P T.hom).pullback P f.left).hasDual
    ((W.pullback P T.hom).pullback P f.left).inverseBundle
    ((W.pullback P T.hom).pullback P f.left).evaluation
    ((W.pullback P T.hom).pullback P f.left).geometry ha

/-- Simultaneous actual Rosati basis equations and the unchanged normalized determinant. -/
def harrisIntegralCMActionCondition (T : Over S)
    (a : O →+* CategoryTheory.End ((baseChange T.hom).obj B)) : Prop :=
  harrisIntegralActionRosatiCondition D C P B W lam T a ∧
    D.HarrisTaylorCMRationalLieDeterminantCondition C (T.hom ≫ p)
      ((baseChange T.hom).obj B)
      (D.harrisHodgePELRationalAction C ((baseChange T.hom).obj B) a)

/-- Integral actions satisfying both equations on the original direct pullback families. -/
def harrisIntegralCMActionSubfunctor :
    Subfunctor (relativeIntegralActionFunctor B basisO) where
  obj T := {a | harrisIntegralCMActionCondition D C P p B W lam T.unop a.down}
  map f a ha :=
    ⟨harrisIntegralActionRosati_restrict D C P B W lam f.unop a.down ha.1,
      D.harrisIntegralActionDeterminant_restrict C p B f.unop a.down ha.2⟩

variable [IsLocallyNoetherian S] (R : Over S)
    [LocallyOfFiniteType R.hom] [IsSeparated R.hom]
    (eR : (locallyNoetherianTestInclusion S).op ⋙
        relativeHomFunctor B.toCommGroupScheme B.toCommGroupScheme ⋙
          forget AddCommGrpCat.{0} ≅
      (locallyNoetherianTestInclusion S).op ⋙ yoneda.obj R)

local notation "raw" => (relativeIntegralActionLocusTest R B basisO eR).obj
local notation "BU" => Functor.obj (baseChange (raw).hom) B
local notation "aU" => relativeIntegralActionUniversal B basisO R eR
local notation "WU" => W.pullback P (raw).hom
local notation "lamU" => W.pullbackMap P (raw).hom WU lam

local instance raw_isLocallyNoetherian : IsLocallyNoetherian (raw).left :=
  (relativeIntegralActionLocusTest R B basisO eR).property

variable
    (H : Over (relativeIntegralActionLocusTest R B
      (D.harrisHodgePELIntegralBasis C) eR).obj.left) [IsSeparated H.hom]
    (eH : (locallyNoetherianTestInclusion
        (relativeIntegralActionLocusTest R B (D.harrisHodgePELIntegralBasis C) eR).obj.left).op ⋙
        relativeHomFunctor
          ((baseChange (relativeIntegralActionLocusTest R B
            (D.harrisHodgePELIntegralBasis C) eR).obj.hom).obj B).toCommGroupScheme
          ((W.pullback P (relativeIntegralActionLocusTest R B
            (D.harrisHodgePELIntegralBasis C) eR).obj.hom).dual P).toCommGroupScheme ⋙
          forget AddCommGrpCat.{0} ≅
      (locallyNoetherianTestInclusion
        (relativeIntegralActionLocusTest R B (D.harrisHodgePELIntegralBasis C) eR).obj.left).op ⋙
        yoneda.obj H)

local notation "cmι" => integralCMEquationLocusι D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability ((raw).hom ≫ p)
  BU (WU).hasDual (WU).inverseBundle (WU).evaluation (WU).geometry H eH aU lamU

/-- The joint equation locus of the actual universal action, as a scheme over the
original base. -/
def harrisIntegralCMActionLocus : Over S := Over.mk (cmι ≫ (raw).hom)

local notation "Z" => harrisIntegralCMActionLocus D C P p B W lam R eR H eH

/-- The actual closed inclusion into the raw integral-action scheme. -/
def harrisIntegralCMActionLocusInclusion : Z ⟶ raw := Over.homMk cmι

local notation "ι" => harrisIntegralCMActionLocusInclusion D C P p B W lam R eR H eH

instance harrisIntegralCMActionLocusInclusion_isClosedImmersion :
    IsClosedImmersion (ι).left := by
  change IsClosedImmersion cmι
  infer_instance

instance harrisIntegralCMActionLocusInclusion_mono : Mono ι :=
  Over.mono_of_mono_left ι

instance harrisIntegralCMActionLocus_locallyOfFiniteType :
    LocallyOfFiniteType (Z).hom := by
  change LocallyOfFiniteType (cmι ≫
    (relativeIntegralActionLocus B basisO R eR
      (relativeEndomorphismPower_isLocallyNoetherian R)).hom)
  infer_instance

instance harrisIntegralCMActionLocus_isSeparated :
    IsSeparated (Z).hom := by
  change IsSeparated (cmι ≫
    (relativeIntegralActionLocus B basisO R eR
      (relativeEndomorphismPower_isLocallyNoetherian R)).hom)
  infer_instance

instance harrisIntegralCMActionLocus_isLocallyNoetherian :
    IsLocallyNoetherian (Z).left :=
  LocallyOfFiniteType.isLocallyNoetherian (Z).hom

variable
    (T : ObjectProperty.FullSubcategory (fun T : Over S => IsLocallyNoetherian T.left))

local notation "classify" => relativeIntegralActionUniversalHomEquiv B basisO R eR T
local notation "cmA" => harrisIntegralCMActionCondition D C P p B W lam T.obj

omit [IsSeparated H.hom] in
/-- A raw classifying map factors through the joint locus precisely when the
classified action on the original direct pullback family satisfies both conditions. -/
theorem harrisIntegralCMActionLocus_factors_iff (f : T.obj ⟶ raw) :
    (∃ k : T.obj ⟶ Z, k ≫ ι = f) ↔ cmA (classify f) := by
  let TU : ObjectProperty.FullSubcategory
      (fun T : Over (raw).left => IsLocallyNoetherian T.left) :=
    ⟨Over.mk f.left, T.property⟩
  let WT := (WU).pullback P f.left
  have heq := integralCMEquationLocus_factors_iff_basis D C P.preservation
    P.composition P.unitCoherence P.associativity P.comparison P.symmetry P.stability
    ((raw).hom ≫ p) BU (WU).hasDual (WU).inverseBundle (WU).evaluation (WU).geometry
    H eH aU lamU P.universality P.compatibility TU
    WT.hasDual WT.inverseBundle WT.evaluation WT.geometry
  have hr := harrisIntegralActionRosati_restrict_iff D C P B W lam f aU
  have hd := D.harrisIntegralActionDeterminant_restrict_iff C p B f aU
  have hd' := D.harrisTaylorCMDeterminantPullbackCondition_iff C ((raw).hom ≫ p) BU
    (D.harrisHodgePELRationalAction C BU aU) f.left
  rw [← D.harrisHodgePELRationalAction_baseChange] at hd'
  have hc := and_congr hr (hd.trans hd')
  change cmA ((relativeEndRestrict B f).comp aU) ↔ _ at hc
  rw [← relativeIntegralActionUniversalHomEquiv_apply B basisO R eR T f] at hc
  constructor
  · rintro ⟨k, hk⟩
    apply hc.mpr
    apply heq.mp
    exact ⟨k.left, congrArg (fun t : T.obj ⟶ raw => t.left) hk⟩
  · intro h
    obtain ⟨k, hk⟩ := heq.mpr (hc.mp h)
    refine ⟨Over.homMk k ?_, ?_⟩
    · change k ≫ (cmι ≫ (raw).hom) = T.obj.hom
      rw [← Category.assoc, hk]
      exact Over.w f
    · apply Over.OverMorphism.ext
      exact hk

/-- Every joint action on the original direct pullback family has a unique actual
classifying morphism. -/
def harrisIntegralCMActionLocusHomEquiv :
    (T.obj ⟶ Z) ≃
      {a : O →+* CategoryTheory.End ((baseChange T.obj.hom).obj B) // cmA a} :=
  Equiv.ofBijective
    (fun k => ⟨classify (k ≫ ι),
      (harrisIntegralCMActionLocus_factors_iff D C P p B W lam R eR H eH T
        (k ≫ ι)).mp ⟨k, rfl⟩⟩)
    (by
      constructor
      · intro k l h
        apply (cancel_mono ι).mp
        exact (classify).injective (congrArg Subtype.val h)
      · rintro ⟨a, ha⟩
        have hf : cmA (classify ((classify).symm a)) := by
          rw [Equiv.apply_symm_apply]
          exact ha
        obtain ⟨k, hk⟩ :=
          (harrisIntegralCMActionLocus_factors_iff D C P p B W lam R eR H eH T
            ((classify).symm a)).mpr hf
        refine ⟨k, Subtype.ext ?_⟩
        change classify (k ≫ ι) = a
        rw [hk, Equiv.apply_symm_apply])

/-- The joint classification is literally restriction of the actual universal action. -/
theorem harrisIntegralCMActionLocusHomEquiv_apply (k : T.obj ⟶ Z) :
    (harrisIntegralCMActionLocusHomEquiv D C P p B W lam R eR H eH T k).val =
      (relativeEndRestrict B (k ≫ ι)).comp aU :=
  relativeIntegralActionUniversalHomEquiv_apply B basisO R eR T (k ≫ ι)

/-- The closed joint locus naturally represents the actual integral-action
subfunctor on the unchanged full locally noetherian test category. -/
def harrisIntegralCMActionLocusIso :
    (locallyNoetherianTestInclusion S).op ⋙ uliftYoneda.{0}.obj Z ≅
      (locallyNoetherianTestInclusion S).op ⋙
        (harrisIntegralCMActionSubfunctor D C P p B W lam).toFunctor :=
  NatIso.ofComponents
    (fun T =>
      let eqv := harrisIntegralCMActionLocusHomEquiv D C P p B W lam R eR H eH T.unop
      let liftEquiv :
          {a : ULift (O →+* CategoryTheory.End ((baseChange T.unop.obj.hom).obj B)) //
            harrisIntegralCMActionCondition D C P p B W lam T.unop.obj a.down} ≃
          {a : O →+* CategoryTheory.End ((baseChange T.unop.obj.hom).obj B) //
            harrisIntegralCMActionCondition D C P p B W lam T.unop.obj a} :=
        Equiv.ulift.subtypeEquiv (fun _ => Iff.rfl)
      ((Equiv.ulift.trans eqv).trans liftEquiv.symm).toIso)
    (by
      intro T T' f
      refine ConcreteCategory.hom_ext _ _ (fun k => ?_)
      apply Subtype.ext
      apply ULift.ext
      change relativeIntegralActionUniversalHomEquiv B basisO R eR T'.unop
          ((f.unop.hom ≫ k.down) ≫ ι) =
        (relativeEndRestrict B f.unop.hom).comp
          (relativeIntegralActionUniversalHomEquiv B basisO R eR T.unop (k.down ≫ ι))
      rw [relativeIntegralActionUniversalHomEquiv_apply,
        relativeIntegralActionUniversalHomEquiv_apply]
      ext x
      change restrict B.toCommGroupScheme B.toCommGroupScheme
          ((f.unop.hom ≫ k.down) ≫ ι) (aU x) =
        restrict B.toCommGroupScheme B.toCommGroupScheme f.unop.hom
          (restrict B.toCommGroupScheme B.toCommGroupScheme (k.down ≫ ι) (aU x))
      rw [Category.assoc]
      exact restrict_comp B.toCommGroupScheme B.toCommGroupScheme
        f.unop.hom (k.down ≫ ι) (aU x))

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel

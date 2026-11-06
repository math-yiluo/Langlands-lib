import Langlands.Shimura.PEL.HarrisIntegralCMFullActionLocus
import Langlands.Shimura.PEL.HarrisIntegralRosatiClosedLocus
import Langlands.Shimura.PEL.HarrisIntegralRosatiComparison
import Langlands.Shimura.PEL.HarrisIntegralActionDeterminantLocus
import Langlands.AbelianScheme.RelativeDualBaseChangeCoherence
import Langlands.AbelianScheme.PolarizedFiniteLevel.Pullback

/-! # Closed classification of full integral Harris actions without mixed Hom representability -/

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

private theorem over_factor_iff {X : Scheme.{0}} {V Z U : Over X}
    (i : Z ⟶ U) (f : V ⟶ U) :
    (∃ k : V ⟶ Z, k ≫ i = f) ↔
      ∃ k : V.left ⟶ Z.left, k ≫ i.left = f.left := by
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k.left, congrArg (fun t : V ⟶ U => t.left) hk⟩
  · rintro ⟨k, hk⟩
    have hw : k ≫ Z.hom = V.hom := by
      rw [← Over.w i, ← Category.assoc, hk, Over.w f]
    refine ⟨Over.homMk k hw, ?_⟩
    apply Over.OverMorphism.ext
    exact hk

section FixedAction

variable [IsLocallyNoetherian S]

local notation "rosatiZ" a₀:max => integralRosatiClosedLocus D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability B W.hasDual
  W.inverseBundle W.evaluation W.geometry a₀ lam
local notation "detι" a₀:max => D.harrisTaylorCMGlobalDeterminantLocusι C p B
  (D.harrisHodgePELRationalAction C B a₀)

private def fixedCMClosedLocus (a : O →+* CategoryTheory.End B) : Over S :=
  Over.mk (pullback.fst (rosatiZ a).hom (detι a) ≫ (rosatiZ a).hom)

local notation "fixedZ" a₀:max => fixedCMClosedLocus D C P p B W lam a₀

private instance fixedCMClosedLocus_isClosedImmersion (a : O →+* CategoryTheory.End B) :
    IsClosedImmersion (fixedZ a).hom := by
  change IsClosedImmersion (pullback.fst (rosatiZ a).hom (detι a) ≫ (rosatiZ a).hom)
  infer_instance

omit [IsLocallyNoetherian S] in
private theorem fixedCMClosedLocus_factors_iff_basis (a : O →+* CategoryTheory.End B)
    (T : Over S) :
    (∃ k : T.left ⟶ (fixedZ a).left, k ≫ (fixedZ a).hom = T.hom) ↔
      IntegralRosatiBasisEquations D C P.preservation P.composition P.unitCoherence
        P.associativity P.comparison P.symmetry P.stability ((baseChange T.hom).obj B)
        (W.pullback P T.hom).hasDual (W.pullback P T.hom).inverseBundle
        (W.pullback P T.hom).evaluation (W.pullback P T.hom).geometry
        (baseChangeOrderAction T.hom B a)
        (W.pullbackMap P T.hom (W.pullback P T.hom) lam) ∧
      D.HarrisTaylorCMRationalLieDeterminantCondition C (T.hom ≫ p)
        ((baseChange T.hom).obj B)
        (D.harrisHodgePELRationalAction C ((baseChange T.hom).obj B)
          (baseChangeOrderAction T.hom B a)) := by
  have hdet := D.harrisTaylorCMGlobalDeterminantLocus_factors_iff C p B
    (D.harrisHodgePELRationalAction C B a) T.hom
  rw [← D.harrisHodgePELRationalAction_baseChange] at hdet
  have hrosati := integralRosatiClosedLocus_nonempty_iff_basis D C P.preservation
    P.composition P.unitCoherence P.associativity P.comparison P.symmetry P.stability
    B W.hasDual W.inverseBundle W.evaluation W.geometry a lam P.universality
    P.compatibility T (W.pullback P T.hom).hasDual (W.pullback P T.hom).inverseBundle
    (W.pullback P T.hom).evaluation (W.pullback P T.hom).geometry
  constructor
  · rintro ⟨k, hk⟩
    have hr : Nonempty (T ⟶ rosatiZ a) :=
      ⟨Over.homMk (k ≫ pullback.fst (rosatiZ a).hom (detι a)) (by
        simpa only [fixedCMClosedLocus, Over.mk_hom, Category.assoc] using hk)⟩
    refine ⟨hrosati.mp hr, hdet.mp ⟨k ≫ pullback.snd (rosatiZ a).hom (detι a), ?_⟩⟩
    rw [Category.assoc, ← pullback.condition, ← Category.assoc]
    exact hk
  · rintro ⟨hr, hd⟩
    obtain ⟨r⟩ := hrosati.mpr hr
    obtain ⟨d, hd⟩ := hdet.mpr hd
    refine ⟨pullback.lift r.left d ((Over.w r).trans hd.symm), ?_⟩
    change pullback.lift r.left d _ ≫
      (pullback.fst (rosatiZ a).hom (detι a) ≫ (rosatiZ a).hom) = _
    rw [← Category.assoc, pullback.lift_fst]
    exact Over.w r

end FixedAction

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

local instance closedRaw_isLocallyNoetherian : IsLocallyNoetherian (raw).left :=
  (relativeIntegralActionLocusTest R B basisO eR).property

local notation "cmι" => (fixedCMClosedLocus D C P ((raw).hom ≫ p) BU WU lamU aU).hom

/-- The joint equation locus of the actual universal action, as a scheme over the
original base. -/
def harrisIntegralCMClosedActionLocus : Over S := Over.mk (cmι ≫ (raw).hom)

local notation "Z" => harrisIntegralCMClosedActionLocus D C P p B W lam R eR

/-- The actual closed inclusion into the raw integral-action scheme. -/
def harrisIntegralCMClosedActionLocusInclusion : Z ⟶ raw := Over.homMk cmι

local notation "ι" => harrisIntegralCMClosedActionLocusInclusion D C P p B W lam R eR

instance harrisIntegralCMClosedActionLocusInclusion_isClosedImmersion :
    IsClosedImmersion (ι).left := by
  change IsClosedImmersion cmι
  infer_instance

instance harrisIntegralCMClosedActionLocusInclusion_mono : Mono ι :=
  Over.mono_of_mono_left ι

instance harrisIntegralCMClosedActionLocus_locallyOfFiniteType :
    LocallyOfFiniteType (Z).hom := by
  change LocallyOfFiniteType (cmι ≫
    (relativeIntegralActionLocus B basisO R eR
      (relativeEndomorphismPower_isLocallyNoetherian R)).hom)
  infer_instance

instance harrisIntegralCMClosedActionLocus_isSeparated :
    IsSeparated (Z).hom := by
  change IsSeparated (cmι ≫
    (relativeIntegralActionLocus B basisO R eR
      (relativeEndomorphismPower_isLocallyNoetherian R)).hom)
  infer_instance

instance harrisIntegralCMClosedActionLocus_isLocallyNoetherian :
    IsLocallyNoetherian (Z).left :=
  LocallyOfFiniteType.isLocallyNoetherian (Z).hom

variable
    (T : ObjectProperty.FullSubcategory (fun T : Over S => IsLocallyNoetherian T.left))

local notation "classify" => relativeIntegralActionUniversalHomEquiv B basisO R eR T
local notation "cmA" => harrisIntegralCMActionCondition D C P p B W lam T.obj

/-- A raw classifying map factors through the joint locus precisely when the
classified action on the original direct pullback family satisfies both conditions. -/
theorem harrisIntegralCMClosedActionLocus_factors_iff (f : T.obj ⟶ raw) :
    (∃ k : T.obj ⟶ Z, k ≫ ι = f) ↔ cmA (classify f) := by
  have heq := fixedCMClosedLocus_factors_iff_basis D C P ((raw).hom ≫ p)
    BU WU lamU aU (Over.mk f.left)
  have hr := harrisIntegralActionRosati_restrict_iff D C P B W lam f aU
  have hd := D.harrisIntegralActionDeterminant_restrict_iff C p B f aU
  have hd' := D.harrisTaylorCMDeterminantPullbackCondition_iff C ((raw).hom ≫ p) BU
    (D.harrisHodgePELRationalAction C BU aU) f.left
  rw [← D.harrisHodgePELRationalAction_baseChange] at hd'
  have hc := and_congr hr (hd.trans hd')
  change cmA ((relativeEndRestrict B f).comp aU) ↔ _ at hc
  rw [← relativeIntegralActionUniversalHomEquiv_apply B basisO R eR T f] at hc
  exact (over_factor_iff ι f).trans (heq.trans hc.symm)

/-- Every joint action on the original direct pullback family has a unique actual
classifying morphism. -/
def harrisIntegralCMClosedActionLocusHomEquiv :
    (T.obj ⟶ Z) ≃
      {a : O →+* CategoryTheory.End ((baseChange T.obj.hom).obj B) // cmA a} :=
  Equiv.ofBijective
    (fun k => ⟨classify (k ≫ ι),
      (harrisIntegralCMClosedActionLocus_factors_iff D C P p B W lam R eR T
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
          (harrisIntegralCMClosedActionLocus_factors_iff D C P p B W lam R eR T
            ((classify).symm a)).mpr hf
        refine ⟨k, Subtype.ext ?_⟩
        change classify (k ≫ ι) = a
        rw [hk, Equiv.apply_symm_apply])

/-- The joint classification is literally restriction of the actual universal action. -/
theorem harrisIntegralCMClosedActionLocusHomEquiv_apply (k : T.obj ⟶ Z) :
    (harrisIntegralCMClosedActionLocusHomEquiv D C P p B W lam R eR T k).val =
      (relativeEndRestrict B (k ≫ ι)).comp aU :=
  relativeIntegralActionUniversalHomEquiv_apply B basisO R eR T (k ≫ ι)

/-- The closed joint locus naturally represents the actual integral-action
subfunctor on the unchanged full locally noetherian test category. -/
def harrisIntegralCMClosedActionLocusIso :
    (locallyNoetherianTestInclusion S).op ⋙ uliftYoneda.{0}.obj Z ≅
      (locallyNoetherianTestInclusion S).op ⋙
        (harrisIntegralCMActionSubfunctor D C P p B W lam).toFunctor :=
  NatIso.ofComponents
    (fun T =>
      let eqv := harrisIntegralCMClosedActionLocusHomEquiv D C P p B W lam R eR T.unop
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

local instance closedTest_isLocallyNoetherian : IsLocallyNoetherian T.obj.left := T.property

/-- The same closed locus imposes all integral-order Rosati equations on every original test. -/
theorem harrisIntegralCMClosedActionLocus_factors_iff_full (f : T.obj ⟶ raw) :
    (∃ k : T.obj ⟶ Z, k ≫ ι = f) ↔
      harrisIntegralCMFullActionCondition D C P p B W lam T.obj (classify f) := by
  rw [harrisIntegralCMFullActionCondition_iff]
  exact harrisIntegralCMClosedActionLocus_factors_iff D C P p B W lam R eR T f

/-- Unique classification with full integral Rosati equations and normalized determinant. -/
def harrisIntegralCMClosedActionLocusFullHomEquiv :
    (T.obj ⟶ Z) ≃
      {a : O →+* CategoryTheory.End ((baseChange T.obj.hom).obj B) //
        harrisIntegralCMFullActionCondition D C P p B W lam T.obj a} :=
  (harrisIntegralCMClosedActionLocusHomEquiv D C P p B W lam R eR T).trans
    (Equiv.subtypeEquivRight (fun a =>
      (harrisIntegralCMFullActionCondition_iff D C P p B W lam T.obj a).symm))

/-- Full-order classification retains literal restriction of the actual universal action. -/
theorem harrisIntegralCMClosedActionLocusFullHomEquiv_apply (k : T.obj ⟶ Z) :
    (harrisIntegralCMClosedActionLocusFullHomEquiv D C P p B W lam R eR T k).val =
      (relativeEndRestrict B (k ≫ ι)).comp aU :=
  harrisIntegralCMClosedActionLocusHomEquiv_apply D C P p B W lam R eR T k

/-- The closed joint locus without a mixed Hom representative naturally represents the full-order action functor. -/
def harrisIntegralCMClosedActionLocusFullIso :
    (locallyNoetherianTestInclusion S).op ⋙ uliftYoneda.{0}.obj Z ≅
      (harrisIntegralCMFullActionSubfunctor D C P p B W lam).toFunctor :=
  harrisIntegralCMClosedActionLocusIso D C P p B W lam R eR ≪≫
    harrisIntegralCMActionBasisFullIso D C P p B W lam

/-- Every classifying morphism yields the published rational involution and determinant. -/
theorem harrisIntegralCMClosedActionLocusFullHomEquiv_involutionCompatible (k : T.obj ⟶ Z) :
    letI := auxiliaryStarRing D C
    let a := (harrisIntegralCMClosedActionLocusFullHomEquiv D C P p B W lam R eR T k).val
    IsInvolutionCompatible P.preservation P.composition P.unitCoherence P.associativity
      P.comparison P.symmetry P.stability (W.pullback P T.obj.hom).hasDual
      (relativeDualSchemeMapAdditivity P.preservation P.stability T.obj.left
        ((baseChange T.obj.hom).obj B) ((baseChange T.obj.hom).obj B)
        (W.pullback P T.obj.hom).hasDual (W.pullback P T.obj.hom).hasDual)
      (W.pullback P T.obj.hom).inverseBundle (W.pullback P T.obj.hom).evaluation
      (W.pullback P T.obj.hom).geometry
      (D.harrisHodgePELRationalAction C ((baseChange T.obj.hom).obj B) a).toRingHom
      (homToHom0 (W.pullbackMap P T.obj.hom (W.pullback P T.obj.hom) lam)) ∧
    D.HarrisTaylorCMRationalLieDeterminantCondition C (T.obj.hom ≫ p)
      ((baseChange T.obj.hom).obj B)
      (D.harrisHodgePELRationalAction C ((baseChange T.obj.hom).obj B) a) :=
  harrisIntegralCMFullActionCondition_involutionCompatible D C P p B W lam T.obj
    (harrisIntegralCMClosedActionLocusFullHomEquiv D C P p B W lam R eR T k).val
    (harrisIntegralCMClosedActionLocusFullHomEquiv D C P p B W lam R eR T k).property


end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel

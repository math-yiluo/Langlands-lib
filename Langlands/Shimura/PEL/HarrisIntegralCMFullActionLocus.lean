import Langlands.Shimura.PEL.HarrisIntegralCMActionLocus
import Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeMapAdditivityProof

/-! # Full-order Rosati classification of the joint Harris action locus -/

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

/-- All actual order equations for the canonical direct pullback of the fixed map. -/
def harrisIntegralActionFullRosatiCondition (T : Over S)
    (a : O →+* CategoryTheory.End ((baseChange T.hom).obj B)) : Prop :=
  IntegralRosatiEquations D C P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability ((baseChange T.hom).obj B)
    (W.pullback P T.hom).hasDual (W.pullback P T.hom).inverseBundle
    (W.pullback P T.hom).evaluation (W.pullback P T.hom).geometry a
    (W.pullbackMap P T.hom (W.pullback P T.hom) lam)

omit [IsScalarTower ℚ F A] in
/-- Published dual additivity identifies the full order equations with the basis equations. -/
theorem harrisIntegralActionFullRosatiCondition_iff (T : Over S)
    [QuasiSeparatedSpace T.left]
    (a : O →+* CategoryTheory.End ((baseChange T.hom).obj B)) :
    harrisIntegralActionFullRosatiCondition D C P B W lam T a ↔
      harrisIntegralActionRosatiCondition D C P B W lam T a := by
  exact integralRosatiEquations_iff_basis D C P.preservation P.composition
    P.unitCoherence P.associativity P.comparison P.symmetry P.stability
    ((baseChange T.hom).obj B) (W.pullback P T.hom).hasDual
    (relativeDualSchemeMapAdditivity P.preservation P.stability T.left
      ((baseChange T.hom).obj B) ((baseChange T.hom).obj B)
      (W.pullback P T.hom).hasDual (W.pullback P T.hom).hasDual)
    (W.pullback P T.hom).inverseBundle (W.pullback P T.hom).evaluation
    (W.pullback P T.hom).geometry a
    (W.pullbackMap P T.hom (W.pullback P T.hom) lam)

/-- Full actual Rosati equations together with the unchanged normalized determinant. -/
def harrisIntegralCMFullActionCondition (T : Over S)
    (a : O →+* CategoryTheory.End ((baseChange T.hom).obj B)) : Prop :=
  harrisIntegralActionFullRosatiCondition D C P B W lam T a ∧
    D.HarrisTaylorCMRationalLieDeterminantCondition C (T.hom ≫ p)
      ((baseChange T.hom).obj B)
      (D.harrisHodgePELRationalAction C ((baseChange T.hom).obj B) a)

/-- Passing from basis equations to full order equations changes no condition. -/
theorem harrisIntegralCMFullActionCondition_iff (T : Over S)
    [QuasiSeparatedSpace T.left]
    (a : O →+* CategoryTheory.End ((baseChange T.hom).obj B)) :
    harrisIntegralCMFullActionCondition D C P p B W lam T a ↔
      harrisIntegralCMActionCondition D C P p B W lam T a :=
  and_congr (harrisIntegralActionFullRosatiCondition_iff D C P B W lam T a) Iff.rfl

/-- Canonical restriction preserves the full order equations and normalized determinant. -/
theorem harrisIntegralCMFullActionCondition_restrict
    {T T' : Over S} [QuasiSeparatedSpace T.left] [QuasiSeparatedSpace T'.left]
    (f : T' ⟶ T) (a : O →+* CategoryTheory.End ((baseChange T.hom).obj B))
    (ha : harrisIntegralCMFullActionCondition D C P p B W lam T a) :
    harrisIntegralCMFullActionCondition D C P p B W lam T'
      ((relativeEndRestrict B f).comp a) := by
  apply (harrisIntegralCMFullActionCondition_iff D C P p B W lam T' _).mpr
  have h := (harrisIntegralCMFullActionCondition_iff D C P p B W lam T a).mp ha
  exact ⟨harrisIntegralActionRosati_restrict D C P B W lam f a h.1,
    D.harrisIntegralActionDeterminant_restrict C p B f a h.2⟩

/-- The full order action conditions define a subfunctor on all locally noetherian tests. -/
def harrisIntegralCMFullActionSubfunctor :
    Subfunctor ((locallyNoetherianTestInclusion S).op ⋙
      relativeIntegralActionFunctor B basisO) where
  obj T := {a | harrisIntegralCMFullActionCondition D C P p B W lam T.unop.obj a.down}
  map {T T'} f a ha := by
    let : IsLocallyNoetherian T.unop.obj.left := T.unop.property
    let : IsLocallyNoetherian T'.unop.obj.left := T'.unop.property
    exact harrisIntegralCMFullActionCondition_restrict D C P p B W lam f.unop.hom a.down ha

/-- The basis and full-order functors agree by the identity on actual actions. -/
def harrisIntegralCMActionBasisFullIso :
    (locallyNoetherianTestInclusion S).op ⋙
        (harrisIntegralCMActionSubfunctor D C P p B W lam).toFunctor ≅
      (harrisIntegralCMFullActionSubfunctor D C P p B W lam).toFunctor :=
  NatIso.ofComponents
    (fun T => by
      letI : IsLocallyNoetherian T.unop.obj.left := T.unop.property
      let eqv :
          {a : ULift (O →+* CategoryTheory.End ((baseChange T.unop.obj.hom).obj B)) //
            harrisIntegralCMActionCondition D C P p B W lam T.unop.obj a.down} ≃
          {a : ULift (O →+* CategoryTheory.End ((baseChange T.unop.obj.hom).obj B)) //
            harrisIntegralCMFullActionCondition D C P p B W lam T.unop.obj a.down} :=
        Equiv.subtypeEquivRight (fun a =>
          (harrisIntegralCMFullActionCondition_iff D C P p B W lam T.unop.obj a.down).symm)
      exact eqv.toIso)
    (by
      intro T T' f
      refine ConcreteCategory.hom_ext _ _ (fun a => ?_)
      rfl)

section Rational

variable (T : Over S) [QuasiSeparatedSpace T.left]

local notation "BT" => Functor.obj (baseChange T.hom) B
local notation "WT" => W.pullback P T.hom
local notation "lamT" => W.pullbackMap P T.hom WT lam
local notation "addT" => relativeDualSchemeMapAdditivity P.preservation P.stability T.left
  BT BT (WT).hasDual (WT).hasDual
local notation "CompatibleT" => IsInvolutionCompatible P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability
  (WT).hasDual addT (WT).inverseBundle (WT).evaluation (WT).geometry

/-- Full integral compatibility yields the published rational involution and determinant. -/
theorem harrisIntegralCMFullActionCondition_involutionCompatible
    (a : O →+* CategoryTheory.End BT)
    (ha : harrisIntegralCMFullActionCondition D C P p B W lam T a) :
    letI := auxiliaryStarRing D C
    CompatibleT (D.harrisHodgePELRationalAction C BT a).toRingHom (homToHom0 lamT) ∧
      D.HarrisTaylorCMRationalLieDeterminantCondition C (T.hom ≫ p) BT
        (D.harrisHodgePELRationalAction C BT a) := by
  let _ := auxiliaryStarRing D C
  have h := (harrisIntegralCMFullActionCondition_iff D C P p B W lam T a).mp ha
  exact ⟨rationalAction_involutionCompatible_of_integralBasis D C P.preservation
    P.composition P.unitCoherence P.associativity P.comparison P.symmetry P.stability
    BT (WT).hasDual addT (WT).inverseBundle (WT).evaluation (WT).geometry a lamT h.1, h.2⟩

/-- Every rational-unit multiple of the fixed map has the same involution compatibility. -/
theorem harrisIntegralCMFullActionCondition_rationalUnitMultiple
    (a : O →+* CategoryTheory.End BT)
    (ha : harrisIntegralCMFullActionCondition D C P p B W lam T a) (q : ℚˣ) :
    letI := auxiliaryStarRing D C
    CompatibleT (D.harrisHodgePELRationalAction C BT a).toRingHom
      (rationalUnitMultiple q (homToHom0 lamT)) := by
  let _ := auxiliaryStarRing D C
  exact (isInvolutionCompatible_rationalUnitMultiple_iff P.preservation P.composition
    P.unitCoherence P.associativity P.comparison P.symmetry P.stability
    (WT).hasDual addT (WT).inverseBundle (WT).evaluation (WT).geometry
    (D.harrisHodgePELRationalAction C BT a).toRingHom (homToHom0 lamT) q).mpr
      (harrisIntegralCMFullActionCondition_involutionCompatible D C P p B W lam T a ha).1

end Rational

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

local instance fullRaw_isLocallyNoetherian : IsLocallyNoetherian (raw).left :=
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

local notation "Z" => harrisIntegralCMActionLocus D C P p B W lam R eR H eH
local notation "ι" => harrisIntegralCMActionLocusInclusion D C P p B W lam R eR H eH

variable
    (T : ObjectProperty.FullSubcategory (fun T : Over S => IsLocallyNoetherian T.left))

local instance test_isLocallyNoetherian : IsLocallyNoetherian T.obj.left := T.property

omit [IsSeparated H.hom] in
/-- The same closed locus detects all actual order equations on each direct test family. -/
theorem harrisIntegralCMFullActionLocus_factors_iff (f : T.obj ⟶ raw) :
    (∃ k : T.obj ⟶ Z, k ≫ ι = f) ↔
      harrisIntegralCMFullActionCondition D C P p B W lam T.obj
        (relativeIntegralActionUniversalHomEquiv B basisO R eR T f) := by
  rw [harrisIntegralCMFullActionCondition_iff]
  exact harrisIntegralCMActionLocus_factors_iff D C P p B W lam R eR H eH T f

/-- Unique classification with full integral Rosati equations and normalized determinant. -/
def harrisIntegralCMFullActionLocusHomEquiv :
    (T.obj ⟶ Z) ≃
      {a : O →+* CategoryTheory.End ((baseChange T.obj.hom).obj B) //
        harrisIntegralCMFullActionCondition D C P p B W lam T.obj a} :=
  (harrisIntegralCMActionLocusHomEquiv D C P p B W lam R eR H eH T).trans
    (Equiv.subtypeEquivRight (fun a =>
      (harrisIntegralCMFullActionCondition_iff D C P p B W lam T.obj a).symm))

/-- Full-order classification retains literal restriction of the actual universal action. -/
theorem harrisIntegralCMFullActionLocusHomEquiv_apply (k : T.obj ⟶ Z) :
    (harrisIntegralCMFullActionLocusHomEquiv D C P p B W lam R eR H eH T k).val =
      (relativeEndRestrict B (k ≫ ι)).comp aU :=
  harrisIntegralCMActionLocusHomEquiv_apply D C P p B W lam R eR H eH T k

/-- The existing closed joint locus naturally represents the full-order action functor. -/
def harrisIntegralCMFullActionLocusIso :
    (locallyNoetherianTestInclusion S).op ⋙ uliftYoneda.{0}.obj Z ≅
      (harrisIntegralCMFullActionSubfunctor D C P p B W lam).toFunctor :=
  harrisIntegralCMActionLocusIso D C P p B W lam R eR H eH ≪≫
    harrisIntegralCMActionBasisFullIso D C P p B W lam

/-- Every classifying morphism yields the published rational involution and determinant. -/
theorem harrisIntegralCMFullActionLocusHomEquiv_involutionCompatible (k : T.obj ⟶ Z) :
    letI := auxiliaryStarRing D C
    let a := (harrisIntegralCMFullActionLocusHomEquiv D C P p B W lam R eR H eH T k).val
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
    (harrisIntegralCMFullActionLocusHomEquiv D C P p B W lam R eR H eH T k).val
    (harrisIntegralCMFullActionLocusHomEquiv D C P p B W lam R eR H eH T k).property

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel

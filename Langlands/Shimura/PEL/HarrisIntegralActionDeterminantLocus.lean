import Langlands.AbelianScheme.RelativeIntegralActionComparison
import Langlands.AbelianScheme.RelativeIntegralActionUniversal
import Langlands.Shimura.PEL.HarrisIntegralOrderActions
import Langlands.Shimura.PEL.HarrisTaylorCMDeterminantGlobalBaseChange

/-! # The normalized determinant locus of the actual universal Harris order action -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Module Opposite
open Langlands.AbelianScheme Langlands.GroupScheme.Cartier

namespace Langlands.Shimura.CentralSimpleUnitaryData

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
    {S : Scheme.{0}} (p : S ⟶ Spec (.of F))
    (B : Langlands.AbelianScheme S)

local notation "O" => D.harrisHodgePELIntegralOrder C
local notation "basisO" => D.harrisHodgePELIntegralBasis C

/-- The normalized determinant on relative restriction is the ordinary pullback condition. -/
theorem harrisIntegralActionDeterminant_restrict_iff
    {T T' : Over S} (f : T' ⟶ T)
    (a : O →+* CategoryTheory.End ((baseChange T.hom).obj B)) :
    D.HarrisTaylorCMRationalLieDeterminantCondition C (T'.hom ≫ p)
        ((baseChange T'.hom).obj B)
        (D.harrisHodgePELRationalAction C ((baseChange T'.hom).obj B)
          ((relativeEndRestrict B f).comp a)) ↔
      D.HarrisTaylorCMDeterminantPullbackCondition C (T.hom ≫ p)
        ((baseChange T.hom).obj B)
        (D.harrisHodgePELRationalAction C ((baseChange T.hom).obj B) a) f.left := by
  have hc := relativeIntegralActionRationalComparison_classOf B basisO f a
  change RationalAlgebraAction.classOf
      (RationalAlgebraAction.of ((baseChange T'.hom).obj B)
        (D.harrisHodgePELRationalAction C ((baseChange T'.hom).obj B)
          ((relativeEndRestrict B f).comp a))) =
    RationalAlgebraAction.pullbackClass f.left
      (RationalAlgebraAction.classOf
        (RationalAlgebraAction.of ((baseChange T.hom).obj B)
          (D.harrisHodgePELRationalAction C ((baseChange T.hom).obj B) a))) at hc
  refine (D.harrisTaylorCMDeterminantClassCondition_classOf C (T'.hom ≫ p)
    (RationalAlgebraAction.of ((baseChange T'.hom).obj B)
      (D.harrisHodgePELRationalAction C ((baseChange T'.hom).obj B)
        ((relativeEndRestrict B f).comp a)))).symm.trans ?_
  unfold HarrisTaylorCMDeterminantPullbackCondition
  rw [← Category.assoc, Over.w f, ← hc]

/-- The full normalized determinant is preserved by canonical relative action restriction. -/
theorem harrisIntegralActionDeterminant_restrict
    {T T' : Over S} (f : T' ⟶ T)
    (a : O →+* CategoryTheory.End ((baseChange T.hom).obj B))
    (ha : D.HarrisTaylorCMRationalLieDeterminantCondition C (T.hom ≫ p)
      ((baseChange T.hom).obj B)
      (D.harrisHodgePELRationalAction C ((baseChange T.hom).obj B) a)) :
    D.HarrisTaylorCMRationalLieDeterminantCondition C (T'.hom ≫ p)
      ((baseChange T'.hom).obj B)
      (D.harrisHodgePELRationalAction C ((baseChange T'.hom).obj B)
        ((relativeEndRestrict B f).comp a)) := by
  apply (D.harrisIntegralActionDeterminant_restrict_iff C p B f a).mpr
  exact D.harrisTaylorCMDeterminantClassCondition_baseChange_of_naturality C
    (T.hom ≫ p) f.left (lieBaseChangeNaturalityStatements T.left).1 _
    ((D.harrisTaylorCMDeterminantClassCondition_classOf C (T.hom ≫ p)
      (RationalAlgebraAction.of ((baseChange T.hom).obj B)
        (D.harrisHodgePELRationalAction C ((baseChange T.hom).obj B) a))).mpr ha)

/-- Actual integral Harris actions satisfying the unchanged normalized determinant. -/
def harrisIntegralDeterminantActionSubfunctor :
    Subfunctor (relativeIntegralActionFunctor B basisO) where
  obj T := {a | D.HarrisTaylorCMRationalLieDeterminantCondition C (T.unop.hom ≫ p)
    ((baseChange T.unop.hom).obj B)
    (D.harrisHodgePELRationalAction C ((baseChange T.unop.hom).obj B) a.down)}
  map f a ha := D.harrisIntegralActionDeterminant_restrict C p B f.unop a.down ha

variable [IsLocallyNoetherian S] (R : Over S)
    [LocallyOfFiniteType R.hom] [IsSeparated R.hom]
    (e : (locallyNoetherianTestInclusion S).op ⋙
        relativeHomFunctor B.toCommGroupScheme B.toCommGroupScheme ⋙
          forget AddCommGrpCat.{0} ≅
      (locallyNoetherianTestInclusion S).op ⋙ yoneda.obj R)

local notation "raw" => (relativeIntegralActionLocusTest R B basisO e).obj
local notation "BU" => Functor.obj (baseChange (raw).hom) B
local notation "aU" => relativeIntegralActionUniversal B basisO R e
local notation "iU" => D.harrisHodgePELRationalAction C BU aU
local notation "detZ" => D.harrisTaylorCMGlobalDeterminantLocus C ((raw).hom ≫ p) BU iU
local notation "detι" => D.harrisTaylorCMGlobalDeterminantLocusι C ((raw).hom ≫ p) BU iU

/-- The actual normalized determinant locus inside the universal integral-action family. -/
def harrisIntegralActionDeterminantLocus : Over S := Over.mk (detι ≫ (raw).hom)

local notation "Z" => D.harrisIntegralActionDeterminantLocus C p B R e

/-- The actual closed inclusion in the raw-action locus. -/
def harrisIntegralActionDeterminantLocusInclusion : Z ⟶ raw := Over.homMk detι

local notation "ι" => D.harrisIntegralActionDeterminantLocusInclusion C p B R e

instance harrisIntegralActionDeterminantLocusInclusion_isClosedImmersion :
    IsClosedImmersion (ι).left := by
  change IsClosedImmersion detι
  infer_instance

instance harrisIntegralActionDeterminantLocusInclusion_mono : Mono ι :=
  Over.mono_of_mono_left ι

instance harrisIntegralActionDeterminantLocus_locallyOfFiniteType :
    LocallyOfFiniteType (Z).hom := by
  change LocallyOfFiniteType (detι ≫
    (relativeIntegralActionLocus B basisO R e
      (relativeEndomorphismPower_isLocallyNoetherian R)).hom)
  infer_instance

instance harrisIntegralActionDeterminantLocus_isSeparated :
    IsSeparated (Z).hom := by
  change IsSeparated (detι ≫
    (relativeIntegralActionLocus B basisO R e
      (relativeEndomorphismPower_isLocallyNoetherian R)).hom)
  infer_instance

instance harrisIntegralActionDeterminantLocus_isLocallyNoetherian :
    IsLocallyNoetherian (Z).left :=
  LocallyOfFiniteType.isLocallyNoetherian (Z).hom

variable
    (T : ObjectProperty.FullSubcategory (fun T : Over S => IsLocallyNoetherian T.left))

local notation "classify" => relativeIntegralActionUniversalHomEquiv B basisO R e T
local notation "detA" => fun a : O →+* CategoryTheory.End ((baseChange T.obj.hom).obj B) =>
  D.HarrisTaylorCMRationalLieDeterminantCondition C (T.obj.hom ≫ p)
    ((baseChange T.obj.hom).obj B)
    (D.harrisHodgePELRationalAction C ((baseChange T.obj.hom).obj B) a)

/-- A raw-action classifying map lifts exactly when its classified direct action satisfies
the published normalized determinant, on the original test representative. -/
theorem harrisIntegralActionDeterminantLocus_factors_iff (f : T.obj ⟶ raw) :
    (∃ k : T.obj ⟶ Z, k ≫ ι = f) ↔ detA (classify f) := by
  have hc : detA (classify f) ↔
      D.HarrisTaylorCMDeterminantPullbackCondition C ((raw).hom ≫ p) BU iU f.left := by
    rw [relativeIntegralActionUniversalHomEquiv_apply]
    exact D.harrisIntegralActionDeterminant_restrict_iff C p B f aU
  constructor
  · rintro ⟨k, hk⟩
    apply hc.mpr
    apply (D.harrisTaylorCMDeterminantPullbackCondition_iff C ((raw).hom ≫ p) BU iU f.left).mpr
    apply (D.harrisTaylorCMGlobalDeterminantLocus_factors_iff C ((raw).hom ≫ p) BU iU f.left).mp
    exact ⟨k.left, congrArg (fun t : T.obj ⟶ raw => t.left) hk⟩
  · intro h
    let hp := hc.mp h
    let k := D.harrisTaylorCMGlobalDeterminantLift C ((raw).hom ≫ p) BU iU f.left hp
    have hk : k ≫ detι = f.left :=
      D.harrisTaylorCMGlobalDeterminantLift_ι C ((raw).hom ≫ p) BU iU f.left hp
    refine ⟨Over.homMk k ?_, ?_⟩
    · change k ≫ (detι ≫ (raw).hom) = T.obj.hom
      rw [← Category.assoc, hk]
      exact Over.w f
    · apply Over.OverMorphism.ext
      exact hk

/-- Every determinant action over the original family has a unique actual classifying map. -/
def harrisIntegralActionDeterminantLocusHomEquiv :
    (T.obj ⟶ Z) ≃ {a : O →+* CategoryTheory.End ((baseChange T.obj.hom).obj B) // detA a} :=
  Equiv.ofBijective
    (fun k => ⟨classify (k ≫ ι),
      (D.harrisIntegralActionDeterminantLocus_factors_iff C p B R e T (k ≫ ι)).mp ⟨k, rfl⟩⟩)
    (by
      constructor
      · intro k l h
        apply (cancel_mono ι).mp
        exact (classify).injective (congrArg Subtype.val h)
      · rintro ⟨a, ha⟩
        have hf : detA (classify ((classify).symm a)) := by
          rw [Equiv.apply_symm_apply]
          exact ha
        obtain ⟨k, hk⟩ :=
          (D.harrisIntegralActionDeterminantLocus_factors_iff C p B R e T
            ((classify).symm a)).mpr hf
        refine ⟨k, Subtype.ext ?_⟩
        change classify (k ≫ ι) = a
        rw [hk, Equiv.apply_symm_apply])

/-- The classification retains the literal universal restriction formula. -/
theorem harrisIntegralActionDeterminantLocusHomEquiv_apply (k : T.obj ⟶ Z) :
    (D.harrisIntegralActionDeterminantLocusHomEquiv C p B R e T k).val =
      (relativeEndRestrict B (k ≫ ι)).comp aU :=
  relativeIntegralActionUniversalHomEquiv_apply B basisO R e T (k ≫ ι)

/-- Actual scheme maps naturally represent determinant integral actions on the full
locally noetherian test category. -/
def harrisIntegralActionDeterminantLocusIso :
    (locallyNoetherianTestInclusion S).op ⋙ uliftYoneda.{0}.obj Z ≅
      (locallyNoetherianTestInclusion S).op ⋙
        (D.harrisIntegralDeterminantActionSubfunctor C p B).toFunctor :=
  NatIso.ofComponents
    (fun T =>
      let eqv := D.harrisIntegralActionDeterminantLocusHomEquiv C p B R e T.unop
      let liftEquiv :
          {a : ULift (O →+* CategoryTheory.End ((baseChange T.unop.obj.hom).obj B)) //
            D.HarrisTaylorCMRationalLieDeterminantCondition C (T.unop.obj.hom ≫ p)
              ((baseChange T.unop.obj.hom).obj B)
              (D.harrisHodgePELRationalAction C ((baseChange T.unop.obj.hom).obj B) a.down)} ≃
          {a : O →+* CategoryTheory.End ((baseChange T.unop.obj.hom).obj B) //
            D.HarrisTaylorCMRationalLieDeterminantCondition C (T.unop.obj.hom ≫ p)
              ((baseChange T.unop.obj.hom).obj B)
              (D.harrisHodgePELRationalAction C ((baseChange T.unop.obj.hom).obj B) a)} :=
        Equiv.ulift.subtypeEquiv (fun _ => Iff.rfl)
      ((Equiv.ulift.trans eqv).trans liftEquiv.symm).toIso)
    (by
      intro T T' f
      refine ConcreteCategory.hom_ext _ _ (fun k => ?_)
      apply Subtype.ext
      apply ULift.ext
      change relativeIntegralActionUniversalHomEquiv B basisO R e T'.unop
          ((f.unop.hom ≫ k.down) ≫ ι) =
        (relativeEndRestrict B f.unop.hom).comp
          (relativeIntegralActionUniversalHomEquiv B basisO R e T.unop (k.down ≫ ι))
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

end Langlands.Shimura.CentralSimpleUnitaryData

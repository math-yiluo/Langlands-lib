import Langlands.Shimura.PEL.HarrisIntegralCMFaithfulAction
import Langlands.Shimura.PEL.HarrisIntegralPrincipalFullLevelNaturality
import Langlands.Shimura.PEL.HarrisPrincipalMarkingActionIso
import Langlands.AbelianScheme.PolarizedFiniteLevel.PullbackCoherence
import Langlands.AbelianScheme.PolarizedFiniteLevel.ZariskiGluingPolarization

/-! # Ordinary marked Harris actions and base change -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false

namespace Langlands.Shimura.PEL.HarrisPolarizedWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme
open Langlands.AbelianScheme.PolarizedFiniteLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.GroupScheme.Cartier
open Langlands.GroupScheme.Tate (Index)

variable {E F A : Type}
    [Field E] [NumberField E] [IsTotallyReal E]
    [Field F] [NumberField F] [IsTotallyComplex F]
    [Algebra E F] [IsQuadraticExtension E F]
    [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
    [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ F A] [IsScalarTower ℚ E F]
    {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
    {L : Type} [Field L] [NumberField L] [IsCMField L]
    [IsQuadraticExtension ℚ L] [Algebra L F]
    {τ₀ : L →+* ℂ}
    (C : HarrisSignatureCharts D.toSecondKindInvolution n
      (harrisCMSection E (algebraMap L F) τ₀))
    (P : Prerequisites.{0})

local notation "O" => D.harrisHodgePELIntegralOrder C
local notation "gH" => Module.finrank ℚ E * n ^ 2

section JointAction

variable {S : Scheme.{0}} (p : S ⟶ Spec (.of F))
    {d : ℕ} (m : Index (fun _ => True)) (a : Datum P S (Module.finrank ℚ E * n ^ 2) d m.val)
    (T : Over S) [QuasiSeparatedSpace T.left] (hT : Nonempty T.left)
    (α : D.harrisHodgePELIntegralOrder C →+*
      CategoryTheory.End ((AbelianScheme.baseChange T.hom).obj a.abelian))
    (hα : harrisIntegralCMFullActionCondition D C P p a.abelian a.dualWitness a.polarization T α)

local notation "PObj" =>
  PositivePolarizedAction D C P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability P.square P.universality (S := T.left)

/-- The positive polarized Harris action on the actual ordinary pullback,
given the full integral action condition on a nonempty test. -/
abbrev harrisOrdinaryJointAction : PObj :=
  harrisIntegralCMFullActionPolarizedActionOfDimension D C P p a.abelian
    a.dualWitness a.polarization a.polarized T hT a.dimension α hα

local notation "X" => harrisOrdinaryJointAction D C P p m a T hT α hα

/-- The integral restriction on the ordinary pulled-back family is the
literal order action from the joint equations. -/
def harrisOrdinaryJointActionRestriction :
    letI := auxiliaryStarRing D C
    PolarizedWeilLevel.IntegralActionRestriction P.preservation P.composition P.unitCoherence
      P.associativity P.comparison P.symmetry P.stability P.square P.universality O X := by
  let := auxiliaryStarRing D C
  exact ⟨α, fun z => congrArg CategoryTheory.End.asHom
    (D.harrisHodgePELRationalAction_coe C (a.pullback T.hom).abelian α z).symm⟩

/-- The marking of the ordinary datum admits an integral Harris frame at
the indicated geometric point of the test. -/
def harrisOrdinaryJointMarkingCompatible
    (compatibility : RelativeFiniteWeilTransitionStatement.{0})
    (h : Global.RationalProfiniteIntegerAdeleComparison)
    {K : Type} [Field K] [IsAlgClosed K] (t : Spec (.of K) ⟶ T.left) : Prop :=
  HarrisPrincipalFullLevelCondition D C h P compatibility t X m (a.pullback T.hom).level

end JointAction

section BaseChange

variable {S : Scheme.{0}} (p : S ⟶ Spec (.of F))
    {d : ℕ} (m : Index (fun _ => True)) (a : Datum P S (Module.finrank ℚ E * n ^ 2) d m.val)
    {T : Over S} [QuasiSeparatedSpace T.left] (hT : Nonempty T.left)
    {S' : Scheme.{0}} [QuasiSeparatedSpace S'] (b : S' ⟶ T.left) (hS' : Nonempty S')

local notation "T'" => Over.mk (b ≫ T.hom)

private local instance pullbackTestQuasiSeparated :
    QuasiSeparatedSpace (Over.mk (b ≫ T.hom)).left :=
  inferInstanceAs (QuasiSeparatedSpace S')

private abbrev pullbackTestMap {T : Over S} (b : S' ⟶ T.left) :
    Over.mk (b ≫ T.hom) ⟶ T := Over.homMk b rfl

local notation "f" => pullbackTestMap (T := T) b

omit [IsScalarTower ℚ E F] in
private theorem pullbackActionCondition
    (action : O →+* CategoryTheory.End ((baseChange T.hom).obj a.abelian))
    (valid : harrisIntegralCMFullActionCondition D C P p a.abelian
      a.dualWitness a.polarization T action) :
    harrisIntegralCMFullActionCondition D C P p a.abelian a.dualWitness a.polarization
      (Over.mk (b ≫ T.hom)) ((relativeEndRestrict a.abelian f).comp action) :=
  harrisIntegralCMFullActionCondition_restrict D C P p a.abelian
    a.dualWitness a.polarization f action valid

local notation "aT" => a.pullback T.hom
local notation "aD" => a.pullback (b ≫ T.hom)
local notation "aC" => (a.pullback T.hom).pullback b
local notation "e" => relativeBaseChangeComparisonIso a.abelian f

omit [IsTotallyReal E] [IsScalarTower ℚ F A] [IsScalarTower ℚ E F] [QuasiSeparatedSpace T.left]
  [QuasiSeparatedSpace S'] in
/-- The relative endomorphism comparison uses the same homomorphism as the
ordinary polarized comparison of direct and successive pullback. -/
theorem relativeBaseChangeComparisonIso_hom_eq_pullbackCompIso :
    (e).hom = (a.pullbackCompIso T.hom b).abelianIso.hom := by
  apply PolarizedFiniteLevel.ZariskiGluing.hom_injective'
  apply pullback.hom_ext
  · change AbelianScheme.hom (e).hom ≫ pullback.fst (pullback.snd a.abelian.X.hom T.hom) b =
      AbelianScheme.hom (baseChangeCompIso T.hom b a.abelian).hom ≫
        pullback.fst (pullback.snd a.abelian.X.hom T.hom) b
    rw [PolarizedFiniteLevel.ZariskiGluing.hom_baseChangeCompIso_fst]
    change (Langlands.GroupScheme.Cartier.baseChangeCompIso a.abelian.toCommGroupScheme
      f).hom.hom.hom.left ≫ pullback.fst (pullback.snd a.abelian.X.hom T.hom) b = _
    refine (Langlands.GroupScheme.Cartier.baseChangeCompIso_hom_fst
      a.abelian.toCommGroupScheme f).trans ?_
    apply pullback.hom_ext <;>
      simp [pullbackTestMap, Langlands.GroupScheme.Cartier.baseChangeProj]
  · exact (Over.w (groupHom (e).hom).hom.hom).trans
      (Over.w (groupHom (a.pullbackCompIso T.hom b).abelianIso.hom).hom.hom).symm

variable (dualityNaturality : DualAbelianBaseChangeNaturalityStatement.{0})
    (compatibility : RelativeFiniteWeilTransitionStatement.{0})
    (h : Global.RationalProfiniteIntegerAdeleComparison)
    {K : Type} [Field K] [IsAlgClosed K] (t : Spec (.of K) ⟶ S')

set_option maxRecDepth 4096 in
include dualityNaturality in
/-- Restriction of an ordinary marked joint action preserves and reflects
its normalized geometric lifting condition at the composite point. -/
theorem harrisOrdinaryJointAction_marking_iff_restrict
    (action : O →+* CategoryTheory.End ((baseChange T.hom).obj a.abelian))
    (valid : harrisIntegralCMFullActionCondition D C P p a.abelian
      a.dualWitness a.polarization T action) :
    harrisOrdinaryJointMarkingCompatible D C P p m a (Over.mk (b ≫ T.hom))
      hS' ((relativeEndRestrict a.abelian f).comp action)
      (pullbackActionCondition D C P p m a (T := T) b action valid) compatibility h t ↔
      harrisOrdinaryJointMarkingCompatible D C P p m a T hT action valid compatibility h
        (t ≫ b) := by
  let := auxiliaryStarRing D C
  let X := harrisOrdinaryJointAction D C P p m a T hT action valid
  let actionD := (relativeEndRestrict a.abelian f).comp action
  let validD := pullbackActionCondition D C P p m a (T := T) b action valid
  let X' := harrisOrdinaryJointAction D C P p m a T' hS' actionD validD
  let LiftD := HarrisPrincipalFullLevelCondition D C h P compatibility t X' m (aD).level
  let Lift := HarrisPrincipalFullLevelCondition D C h P compatibility (t ≫ b) X m (aT).level
  change LiftD ↔ Lift
  let WC := (aC).dualWitness
  let W : PositivePullbackDualData D C P.preservation P.composition P.unitCoherence
      P.associativity P.comparison P.symmetry P.stability P.square P.universality b X :=
    ⟨WC.hasDual, WC.geometry, WC.inverseBundle, WC.evaluation,
      relativeDualSchemeMapAdditivity P.preservation P.stability S'
        (aC).abelian (aC).abelian WC.hasDual WC.hasDual⟩
  let := scalarExtensionAlgebraModule A A (Global.FiniteAdeles ℚ)
  let V := (Global.FiniteAdeles ℚ) ⊗[ℚ] A
  let Frame := Tate.AdelicFrame (aT).abelian h
    (D.harrisHodgePELRationalAction C (aT).abelian action) V (t ≫ b)
  have compare (hex : Nonempty Frame) : LiftD ↔ Lift := by
    let Y := framedPositiveActionBaseChange D C P.preservation P.composition
      P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
      dualityNaturality P.polarizationBaseChange b X W.hasDual W.geometry W.inversePoincare
      W.evaluation W.dualEndAdditivity h t hex
    let aX' := harrisOrdinaryJointActionRestriction D C P p m a T' hS' actionD validD
    let aY : PolarizedWeilLevel.IntegralActionRestriction P.preservation P.composition
        P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square
        P.universality O Y := by
      refine ⟨baseChangeOrderAction b (aT).abelian action, ?_⟩
      intro z
      change homToHom0 ((baseChange b).map (action z).asHom) =
        rationalBaseChangeHom b (D.harrisHodgePELRationalAction C (aT).abelian action (z : A)).asHom
      rw [D.harrisHodgePELRationalAction_coe]
      exact (rationalBaseChangeHom_ofHom b (action z).asHom).symm
    have he (z : O) :
        (aX'.action z).asHom ≫ (e).hom = (e).hom ≫ (aY.action z).asHom :=
      relativeEndRestrict_comparison_intertwines a.abelian f (action z)
    have hcomp := relativeBaseChangeComparisonIso_hom_eq_pullbackCompIso (T := T) P m a b
    have hpol : (X').polarization =
        DualWitness.transportMap P e
          (PolarizedWeilLevel.PolarizedAction.dualWitness P X')
          (PolarizedWeilLevel.PolarizedAction.dualWitness P Y) Y.polarization := by
      change (aD).polarization = (e).hom ≫ (aC).polarization ≫
        (aD).dualWitness.map P (aC).dualWitness (e).hom
      exact (a.pullbackCompIso T.hom b).polarization_eq.trans
        (congrArg (fun u : (aD).abelian ⟶ (aC).abelian =>
          u ≫ (aC).polarization ≫ (aD).dualWitness.map P (aC).dualWitness u) hcomp.symm)
    have hlevel (j : Fin (2 * gH)) :
        levelIsoLinear e (Over.mk (𝟙 S')) m.val ((aD).level.sections j) =
          (aC).level.sections j := by
      change mapTuple (e).hom (aD).level.sections j = _
      exact (congrArg (fun u : (aD).abelian ⟶ (aC).abelian =>
        mapTuple u (aD).level.sections j) hcomp).trans ((a.pullbackCompIso T.hom b).level_eq j)
    let add := HarrisTaylorCMWeilLevel.positivePairAdditivity D C
      P.preservation P.composition P.unitCoherence P.associativity P.comparison P.symmetry
      P.stability P.square P.universality (S := S')
    exact (harrisPrincipalFullLevelCondition_iff_actionIso D C P X' Y e aX' aY he
      compatibility h t add hpol m (aD).level (aC).level hlevel).trans
      (harrisPrincipalFullLevelCondition_iff_baseChange D C P compatibility h
        dualityNaturality P.polarizationBaseChange b t X W hex m (aT).level)
  constructor
  · intro hv
    refine (compare ?_).mp hv
    obtain ⟨eta, -, -⟩ := hv
    let eRat := relativeIntegralActionRationalComparisonIso a.abelian
      (D.harrisHodgePELIntegralBasis C) f action
    exact ⟨Tate.adelicFrameBaseChange b (aT).abelian h
      (D.harrisHodgePELRationalAction C (aT).abelian action) _ t
      (Tate.adelicFrameIsogeny h _ _ _ t (RationalAlgebraAction.underlyingIso eRat)
        (RationalAlgebraAction.intertwines eRat.hom) eta.val)⟩
  · intro hv
    obtain ⟨eta, hn, hl⟩ := hv
    exact (compare ⟨eta.val⟩).mpr ⟨eta, hn, hl⟩

end BaseChange

section TestMaps

variable {S : Scheme.{0}} (p : S ⟶ Spec (.of F))
    {d : ℕ} (m : Index (fun _ => True)) (a : Datum P S (Module.finrank ℚ E * n ^ 2) d m.val)
    {T T' : Over S} [QuasiSeparatedSpace T.left] [qsT' : QuasiSeparatedSpace T'.left]
    (hT : Nonempty T.left) (hT' : Nonempty T'.left) (f : T' ⟶ T)
    (dualityNaturality : DualAbelianBaseChangeNaturalityStatement.{0})
    (compatibility : RelativeFiniteWeilTransitionStatement.{0})
    (h : Global.RationalProfiniteIntegerAdeleComparison)

include dualityNaturality in
/-- The geometric reflection comparison for an arbitrary map in the slice. -/
theorem harrisOrdinaryJointMarkingCompatible_restrict
    (action : O →+* CategoryTheory.End ((baseChange T.hom).obj a.abelian))
    (valid : harrisIntegralCMFullActionCondition D C P p a.abelian
      a.dualWitness a.polarization T action)
    {K : Type} [Field K] [IsAlgClosed K] (t : Spec (.of K) ⟶ T'.left) :
    harrisOrdinaryJointMarkingCompatible D C P p m a T' hT'
      ((relativeEndRestrict a.abelian f).comp action)
      (harrisIntegralCMFullActionCondition_restrict D C P p a.abelian
        a.dualWitness a.polarization f action valid) compatibility h t ↔
    harrisOrdinaryJointMarkingCompatible D C P p m a T hT
      action valid compatibility h (t ≫ f.left) := by
  obtain ⟨Y, q, rfl⟩ := Over.mk_surjective T'
  obtain ⟨b, hb, rfl⟩ := Over.homMk_surjective f
  change QuasiSeparatedSpace Y at qsT'
  change Nonempty Y at hT'
  change Spec (.of K) ⟶ Y at t
  change Y ⟶ T.left at b
  change b ≫ T.hom = q at hb
  subst q
  exact harrisOrdinaryJointAction_marking_iff_restrict D C P p m a hT b hT'
    dualityNaturality compatibility h t action valid

end TestMaps

section Point

open Langlands.AlgebraicGeometry.FiniteEtale
open Langlands.GroupScheme (mu muFiniteEtale)
open HarrisTaylorCMWeilLevel (HarrisGeometricPoint cmBaseTorsionUnit)

variable {S : Scheme.{0}} (p : S ⟶ Spec (.of F))
    {d : ℕ} (m : Index (fun _ => True)) (a : Datum P S (Module.finrank ℚ E * n ^ 2) d m.val)
    (T : Over S) [QuasiSeparatedSpace T.left] [IsLocallyNoetherian T.left] [ConnectedSpace T.left]
    (compatibility : RelativeFiniteWeilTransitionStatement.{0})
    (h : Global.RationalProfiniteIntegerAdeleComparison)
    (htor : TorsionFiniteEtaleStatement.{0})

set_option maxRecDepth 4096 in
include htor in
/-- The compatible marking of a fixed marked action on a connected test
can be checked at any geometric point of that test. -/
theorem harrisOrdinaryJointMarkingCompatible_iff_point
    (action : O →+* CategoryTheory.End ((AbelianScheme.baseChange T.hom).obj a.abelian))
    (valid : harrisIntegralCMFullActionCondition D C P p a.abelian
      a.dualWitness a.polarization T action)
    (U : FiniteAdelicScalarExtensionLevel A A (D.harrisHodgePELForm C))
    (hU : U.toSubgroup = harrisIntegralAdeleCongruence D C m.val)
    (s t : HarrisGeometricPoint T.left) :
    harrisOrdinaryJointMarkingCompatible D C P p m a T (inferInstance : Nonempty T.left)
      action valid compatibility h (K := s.Ω) s.hom ↔
    harrisOrdinaryJointMarkingCompatible D C P p m a T (inferInstance : Nonempty T.left)
      action valid compatibility h (K := t.Ω) t.hom := by
  let hu := cmBaseTorsionUnit (T.hom ≫ p)
  let : ∀ k : Index (fun _ => True), IsFinite (mu T.left k.val).X.hom :=
    fun k => (muFiniteEtale T.left k.val k.property.1 (hu k)).1
  let : ∀ k : Index (fun _ => True), Etale (mu T.left k.val).X.hom :=
    fun k => (muFiniteEtale T.left k.val k.property.1 (hu k)).2
  let X := harrisOrdinaryJointAction D C P p m a T (inferInstance : Nonempty T.left) action valid
  exact harrisPrincipalFullLevelCondition_iff_point D C P compatibility h htor hu
    (s := s.hom) (t := t.hom) (hs := s.finiteFibers) (ht := t.finiteFibers)
    X m U hU (a.pullback T.hom).level

end Point

section Pointwise

open Opposite
open HarrisTaylorCMWeilLevel (HarrisGeometricPoint)

variable {S : Scheme.{0}} (p : S ⟶ Spec (.of F))
    {d : ℕ} (m : Index (fun _ => True)) (a : Datum P S (Module.finrank ℚ E * n ^ 2) d m.val)
    (compatibility : RelativeFiniteWeilTransitionStatement.{0})
    (h : Global.RationalProfiniteIntegerAdeleComparison)

/-- Compatibility of the actual ordered marking with the Harris action at
every geometric point of the test. The empty test has no marking conditions. -/
def harrisOrdinaryPointwiseMarking (T : Over S) [QuasiSeparatedSpace T.left]
    (action : O →+* CategoryTheory.End ((AbelianScheme.baseChange T.hom).obj a.abelian))
    (valid : harrisIntegralCMFullActionCondition D C P p a.abelian
      a.dualWitness a.polarization T action) : Prop :=
  ∀ s : HarrisGeometricPoint T.left,
    harrisOrdinaryJointMarkingCompatible D C P p m a T
      ⟨s.hom (IsLocalRing.closedPoint s.Ω)⟩ action valid compatibility h (K := s.Ω) s.hom

variable (dualityNaturality : DualAbelianBaseChangeNaturalityStatement.{0})

include dualityNaturality in
/-- Restriction preserves pointwise compatibility of the actual marking. -/
theorem harrisOrdinaryPointwiseMarking_restrict
    {T T' : Over S} [QuasiSeparatedSpace T.left] [QuasiSeparatedSpace T'.left]
    (f : T' ⟶ T)
    (action : O →+* CategoryTheory.End ((AbelianScheme.baseChange T.hom).obj a.abelian))
    (valid : harrisIntegralCMFullActionCondition D C P p a.abelian
      a.dualWitness a.polarization T action)
    (marked : harrisOrdinaryPointwiseMarking D C P p m a compatibility h T action valid) :
    harrisOrdinaryPointwiseMarking D C P p m a compatibility h T'
      ((relativeEndRestrict a.abelian f).comp action)
      (harrisIntegralCMFullActionCondition_restrict D C P p a.abelian
        a.dualWitness a.polarization f action valid) := by
  intro s
  let x := s.hom (IsLocalRing.closedPoint s.Ω)
  exact (harrisOrdinaryJointMarkingCompatible_restrict D C P p m a
    ⟨f.left x⟩ ⟨x⟩ f dualityNaturality compatibility h action valid
    (K := s.Ω) s.hom).mpr (marked (s.comp f.left))

/-- The subfunctor of actual actions on the ordinary datum whose markings
are compatible on all geometric points of each locally noetherian test. -/
def harrisOrdinaryMarkedActionSubfunctor :
    Subfunctor (harrisIntegralCMFullActionSubfunctor D C P p a.abelian
      a.dualWitness a.polarization).toFunctor where
  obj T := {v | by
    let : IsLocallyNoetherian T.unop.obj.left := T.unop.property
    exact harrisOrdinaryPointwiseMarking D C P p m a compatibility h T.unop.obj
      v.val.down v.property}
  map {T T'} f v hv := by
    let : IsLocallyNoetherian T.unop.obj.left := T.unop.property
    let : IsLocallyNoetherian T'.unop.obj.left := T'.unop.property
    exact harrisOrdinaryPointwiseMarking_restrict D C P p m a compatibility h
      dualityNaturality f.unop.hom v.val.down v.property hv

end Pointwise

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel

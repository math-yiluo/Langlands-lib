import Langlands.Shimura.PEL.HarrisCMOrdinaryMarkedAction
import Langlands.GroupScheme.Cartier.BaseChange
import Langlands.Shimura.PEL.HarrisIntegralRosatiComparison

/-! # Changing the base of the ordinary marked Harris action functor -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false

namespace Langlands.AbelianScheme

open Langlands.GroupScheme.Cartier

universe u

variable {S S' : Scheme.{u}} (B : AbelianScheme S) (b : S' ⟶ S)

/-- Actual relative endomorphism rings on the direct and successive pullbacks
are identified by the canonical Hom comparison. -/
def relativeEndBaseChangeEquiv (T : Over S') :
    CategoryTheory.End ((baseChange ((Over.map b).obj T).hom).obj B) ≃+*
      CategoryTheory.End ((baseChange T.hom).obj ((baseChange b).obj B)) := by
  let e := relativeHomBaseChangeEquiv B.toCommGroupScheme B.toCommGroupScheme b T
  let c := baseChangeCompIso b T.hom B
  refine
    { toFun := fun x => CategoryTheory.End.of (e x.asHom)
      invFun := fun x => CategoryTheory.End.of (e.symm x.asHom)
      left_inv := fun x => CategoryTheory.End.ext (e.symm_apply_apply x.asHom)
      right_inv := fun x => CategoryTheory.End.ext (e.apply_symm_apply x.asHom)
      map_add' := fun x y => CategoryTheory.End.ext (e.map_add x.asHom y.asHom)
      map_mul' := ?_ }
  intro x y
  apply CategoryTheory.End.ext
  change c.inv ≫ (y.asHom ≫ x.asHom) ≫ c.hom =
    (c.inv ≫ y.asHom ≫ c.hom) ≫ c.inv ≫ x.asHom ≫ c.hom
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- The actual direct-to-successive isomorphism intertwines each endomorphism. -/
theorem relativeEndBaseChangeEquiv_intertwines (T : Over S')
    (x : CategoryTheory.End ((baseChange ((Over.map b).obj T).hom).obj B)) :
    x.asHom ≫ (baseChangeCompIso b T.hom B).hom =
      (baseChangeCompIso b T.hom B).hom ≫ (relativeEndBaseChangeEquiv B b T x).asHom := by
  let c := baseChangeCompIso b T.hom B
  change x.asHom ≫ c.hom = c.hom ≫ c.inv ≫ x.asHom ≫ c.hom
  rw [Iso.hom_inv_id_assoc]

/-- The endomorphism comparison on each test commutes with relative restriction. -/
theorem relativeEndBaseChangeEquiv_restrict {T T' : Over S'} (f : T' ⟶ T)
    (x : CategoryTheory.End ((baseChange ((Over.map b).obj T).hom).obj B)) :
    relativeEndBaseChangeEquiv B b T' (relativeEndRestrict B ((Over.map b).map f) x) =
      relativeEndRestrict ((baseChange b).obj B) f (relativeEndBaseChangeEquiv B b T x) := by
  apply CategoryTheory.End.ext
  exact relativeHomBaseChangeEquiv_restrict B.toCommGroupScheme B.toCommGroupScheme
    b f x.asHom

end Langlands.AbelianScheme

namespace Langlands.Shimura.PEL.HarrisPolarizedWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme
open Langlands.AbelianScheme.PolarizedFiniteLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.GroupScheme.Tate (Index)
open HarrisTaylorCMWeilLevel (HarrisGeometricPoint)

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
    {S S' : Scheme.{0}} (p : S ⟶ Spec (.of F)) (b : S' ⟶ S)
    {d : ℕ} (m : Index (fun _ => True))
    (a : Datum P S (Module.finrank ℚ E * n ^ 2) d m.val)
    (T : Over S')

local notation "O" => D.harrisHodgePELIntegralOrder C
local notation "T₀" => (Over.map b).obj T
local notation "a₀" => a.pullback (T.hom ≫ b)
local notation "a₁" => (a.pullback b).pullback T.hom
local notation "W₀" => (a₀).dualWitness
local notation "W₁" => (a₁).dualWitness
local notation "comparison" => a.pullbackCompIso b T.hom
local notation "e" => (comparison).abelianIso
local notation "endEquiv" => relativeEndBaseChangeEquiv a.abelian b T
local notation "changeAction" α:max => (endEquiv).toRingHom.comp α

omit [IsScalarTower ℚ E F] in
/-- Pullback composition transports both the full integral Rosati equations
and the normalized determinant with the same map to the CM base. -/
theorem harrisOrdinaryJointActionCondition_baseChange_iff
    (action : O →+* CategoryTheory.End ((AbelianScheme.baseChange ((Over.map b).obj T).hom).obj
      a.abelian)) :
    harrisIntegralCMFullActionCondition D C P p a.abelian a.dualWitness a.polarization
      T₀ action ↔
    harrisIntegralCMFullActionCondition D C P (b ≫ p) (a.pullback b).abelian
      (a.pullback b).dualWitness (a.pullback b).polarization T (changeAction action) := by
  let action' := changeAction action
  have he (x : O) : (action x).asHom ≫ (e).hom = (e).hom ≫ (action' x).asHom :=
    relativeEndBaseChangeEquiv_intertwines a.abelian b T (action x)
  refine and_congr ?_ ?_
  · have hh := integralRosatiEquations_comparison_iff D C P.preservation P.composition
      P.unitCoherence P.associativity P.comparison P.symmetry P.stability
      (W₁).hasDual (W₁).inverseBundle (W₁).evaluation (W₁).geometry
      (W₀).hasDual (W₀).inverseBundle (W₀).evaluation (W₀).geometry
      e action' action he (a₁).polarization
    have hpol : (a₀).polarization =
        integralRosatiComparisonMap P.preservation P.composition P.unitCoherence
          P.associativity P.comparison P.symmetry P.stability
          (W₁).hasDual (W₁).inverseBundle (W₁).evaluation (W₁).geometry
          (W₀).hasDual (W₀).inverseBundle (W₀).evaluation (W₀).geometry e (a₁).polarization :=
      (comparison).polarization_eq
    rw [← hpol] at hh
    exact hh
  · let i := D.harrisHodgePELRationalAction C (a₀).abelian action
    let i' := D.harrisHodgePELRationalAction C (a₁).abelian action'
    have hlinear (x : A) :
        comp0 (a₀).abelian (a₀).abelian (a₁).abelian (i x).asHom (homToHom0 (e).hom) =
          comp0 (a₀).abelian (a₁).abelian (a₁).abelian (homToHom0 (e).hom) (i' x).asHom :=
      integralActionRationalExtension_intertwines (B := (a₀).abelian) (C := (a₁).abelian)
        (D.harrisHodgePELIntegralBasis C) action action' (e).hom he x
    change D.HarrisTaylorCMRationalLieDeterminantCondition C ((T.hom ≫ b) ≫ p)
        (a₀).abelian i ↔
      D.HarrisTaylorCMRationalLieDeterminantCondition C (T.hom ≫ b ≫ p)
        (a₁).abelian i'
    rw [Category.assoc]
    exact D.harrisTaylorCMRationalLieDeterminantCondition_iso C (T.hom ≫ b ≫ p) i i'
      (Rationalization.inclusion.mapIso e) hlinear

section Marking

variable (compatibility : RelativeFiniteWeilTransitionStatement.{0})
    (h : Global.RationalProfiniteIntegerAdeleComparison) [QuasiSeparatedSpace T.left]

private local instance : QuasiSeparatedSpace ((Over.map b).obj T).left :=
  inferInstanceAs (QuasiSeparatedSpace T.left)

set_option maxRecDepth 4096 in
/-- The direct and successive marked actions have the same geometric
compatibility condition on the test. -/
theorem harrisOrdinaryPointwiseMarking_baseChange_iff
    (action : O →+* CategoryTheory.End ((AbelianScheme.baseChange ((Over.map b).obj T).hom).obj
      a.abelian))
    (valid : harrisIntegralCMFullActionCondition D C P p a.abelian a.dualWitness a.polarization
      T₀ action)
    (valid' : harrisIntegralCMFullActionCondition D C P (b ≫ p) (a.pullback b).abelian
      (a.pullback b).dualWitness (a.pullback b).polarization T (changeAction action)) :
    harrisOrdinaryPointwiseMarking D C P p m a compatibility h T₀ action valid ↔
      harrisOrdinaryPointwiseMarking D C P (b ≫ p) m (a.pullback b) compatibility h T
        (changeAction action) valid' := by
  refine forall_congr' fun s => ?_
  let := auxiliaryStarRing D C
  let ne : Nonempty T.left := ⟨s.hom (IsLocalRing.closedPoint s.Ω)⟩
  let X := harrisOrdinaryJointAction D C P p m a T₀ ne action valid
  let Y := harrisOrdinaryJointAction D C P (b ≫ p) m (a.pullback b) T ne
    (changeAction action) valid'
  let actX := harrisOrdinaryJointActionRestriction D C P p m a T₀ ne action valid
  let actY := harrisOrdinaryJointActionRestriction D C P (b ≫ p) m (a.pullback b) T ne
    (changeAction action) valid'
  have he (x : O) : (actX.action x).asHom ≫ (e).hom = (e).hom ≫ (actY.action x).asHom :=
    relativeEndBaseChangeEquiv_intertwines a.abelian b T (action x)
  let add := HarrisTaylorCMWeilLevel.positivePairAdditivity D C
    P.preservation P.composition P.unitCoherence P.associativity P.comparison P.symmetry
    P.stability P.square P.universality (S := T.left)
  have hpol : X.polarization = DualWitness.transportMap P e
      (PolarizedWeilLevel.PolarizedAction.dualWitness P X)
      (PolarizedWeilLevel.PolarizedAction.dualWitness P Y) Y.polarization :=
    (comparison).polarization_eq
  exact harrisPrincipalFullLevelCondition_iff_actionIso D C P X Y e actX actY he
    compatibility h (Ω := s.Ω) s.hom add hpol m (a₀).level (a₁).level (comparison).level_eq

end Marking

section Functors

local notation "Tests" S₀:max => ObjectProperty.FullSubcategory
  (fun T : Over S₀ => IsLocallyNoetherian T.left)

/-- Compose a locally noetherian test with the morphism of base schemes. -/
def locallyNoetherianTestMap : Tests S' ⥤ Tests S where
  obj Q := ⟨(Over.map b).obj Q.obj, Q.property⟩
  map f := ObjectProperty.homMk ((Over.map b).map f.hom)
  map_id _ := rfl
  map_comp _ _ := rfl

variable (compatibility : RelativeFiniteWeilTransitionStatement.{0})
    (h : Global.RationalProfiniteIntegerAdeleComparison)
    (dualityNaturality : DualAbelianBaseChangeNaturalityStatement.{0})

local notation "globalFunctor" => (locallyNoetherianTestMap b).op ⋙
  (harrisOrdinaryMarkedActionSubfunctor D C P p m a compatibility h dualityNaturality).toFunctor
local notation "localFunctor" => (harrisOrdinaryMarkedActionSubfunctor D C P (b ≫ p) m
  (a.pullback b) compatibility h dualityNaturality).toFunctor

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4500000 in
private def markedActionBaseChangeEquiv (Q : Tests S') :
    (globalFunctor).obj (op Q) ≃ (localFunctor).obj (op Q) := by
  let U := Q.obj
  let U₀ := (Over.map b).obj U
  let : IsLocallyNoetherian U.left := Q.property
  let : IsLocallyNoetherian U₀.left := Q.property
  let : QuasiSeparatedSpace U.left := inferInstance
  let : QuasiSeparatedSpace U₀.left := inferInstanceAs (QuasiSeparatedSpace U.left)
  let Actions₀ := ULift.{0} (O →+* CategoryTheory.End
    ((AbelianScheme.baseChange U₀.hom).obj a.abelian))
  let Actions₁ := ULift.{0} (O →+* CategoryTheory.End
    ((AbelianScheme.baseChange U.hom).obj (a.pullback b).abelian))
  let endComparison := relativeEndBaseChangeEquiv a.abelian b U
  let e₀ : Actions₀ ≃ Actions₁ :=
    { toFun := fun x => ULift.up (endComparison.toRingHom.comp x.down)
      invFun := fun x => ULift.up (endComparison.symm.toRingHom.comp x.down)
      left_inv := fun x => ULift.ext (RingHom.ext fun z => endComparison.symm_apply_apply (x.down z))
      right_inv := fun x => ULift.ext (RingHom.ext fun z => endComparison.apply_symm_apply (x.down z)) }
  let valid₀ (x : Actions₀) : Prop := harrisIntegralCMFullActionCondition D C P p
    a.abelian a.dualWitness a.polarization U₀ x.down
  let valid₁ (x : Actions₁) : Prop := harrisIntegralCMFullActionCondition D C P (b ≫ p)
    (a.pullback b).abelian (a.pullback b).dualWitness (a.pullback b).polarization U x.down
  let e₁ : Subtype valid₀ ≃ Subtype valid₁ :=
    e₀.subtypeEquiv (fun x =>
      harrisOrdinaryJointActionCondition_baseChange_iff D C P p b m a U x.down)
  let marked₀ (x : Subtype valid₀) : Prop := harrisOrdinaryPointwiseMarking D C P p m a
    compatibility h U₀ x.val.down x.property
  let marked₁ (x : Subtype valid₁) : Prop := harrisOrdinaryPointwiseMarking D C P (b ≫ p) m
    (a.pullback b) compatibility h U x.val.down x.property
  change Subtype marked₀ ≃ Subtype marked₁
  refine e₁.subtypeEquiv (fun x => ?_)
  exact harrisOrdinaryPointwiseMarking_baseChange_iff D C P p b m a U compatibility h
    x.val.down x.property (e₁ x).property

/-- Changing the base of the marked action problem gives the natural
comparison on all locally noetherian tests of the changed base. -/
def harrisOrdinaryMarkedActionBaseChangeIso : globalFunctor ≅ localFunctor :=
  NatIso.ofComponents
    (fun Q => (markedActionBaseChangeEquiv D C P p b m a compatibility h dualityNaturality
      Q.unop).toIso)
    (by
      intro Q Q' f
      refine ConcreteCategory.hom_ext _ _ (fun x => ?_)
      apply Subtype.ext
      apply Subtype.ext
      apply ULift.ext
      apply RingHom.ext
      intro z
      exact relativeEndBaseChangeEquiv_restrict a.abelian b f.unop.hom (x.val.val.down z))

end Functors

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel

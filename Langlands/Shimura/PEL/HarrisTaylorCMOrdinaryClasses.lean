import Langlands.Shimura.PEL.HarrisTaylorCMOrdinaryIsomorphisms
import Langlands.Shimura.PEL.HarrisTaylorCMTateBaseChange

/-! # Ordinary classes and actual transport of full Tate-normalized CM models -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme
open Langlands.AbelianScheme.PolarizedFiniteLevel
open HarrisPolarizedWeilLevel HarrisNumericalWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.FiniteEtale Langlands.GroupScheme

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F] [IsCMField F]
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
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  (htor : TorsionFiniteEtaleStatement.{0})

local notation "Bases" => AdmissibleCMBaseCategory D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
local notation "NRepAt" X:max a:max =>
  TateNormalizedCMRepresentative D C P X compatibility h (a).hom (a).finiteFibers htor
local notation "NClassesAt" X:max a:max =>
  TateNormalizedCMIsoClass D C P X compatibility h (a).hom (a).finiteFibers htor
local notation "ordinaryRel" X:max a:max =>
  TateNormalizedCMOrdinaryRelated D C P X compatibility h (a).hom (a).finiteFibers htor
local notation "relIff" X:max a:max =>
  tateNormalizedCMRelated_iff_ordinaryRelated D C P X compatibility h
    (a).hom (a).finiteFibers htor
local notation "classIff" X:max a:max =>
  tateNormalizedCMRepresentativeClass_eq_iff_ordinaryRelated D C P X compatibility h
    (a).hom (a).finiteFibers htor
local notation "repClassAt" X:max a:max =>
  tateNormalizedCMRepresentativeClass D C P X compatibility h (a).hom (a).finiteFibers htor
local notation "nForget" X:max a:max =>
  tateNormalizedCMForget D C P X compatibility h (a).hom (a).finiteFibers htor
local notation "lev" U:max => (hodgeLevelFunctor D C).obj U
local notation "NMove" X:max a:max b:max path:max =>
  tateNormalizedCMClassPointMap D C P X compatibility h htor
    (s := (a).hom) (t := (b).hom) (hs := (a).finiteFibers) (ht := (b).finiteFibers) path

/-- At an integral source-stabilizing level, ordinary actual isomorphism is an
 equivalence relation on the existing full Tate-normalized models. -/
def tateNormalizedCMOrdinarySetoid (X : Bases) (a : HarrisGeometricPoint X.obj.left)
    (U : HarrisLevel D) (hU : (lev U).toSubgroup ≤ harrisIntegralAdeleStabilizer D C) :
    Setoid ((NRepAt X a) U) where
  r := ordinaryRel X a
  iseqv := ⟨fun x => ((classIff X a) hU x x).mp rfl,
    fun {x y} hxy => ((classIff X a) hU y x).mp
      (((classIff X a) hU x y).mpr hxy).symm,
    fun {x y z} hxy hyz => ((classIff X a) hU x z).mp
      ((((classIff X a) hU x y).mpr hxy).trans
        (((classIff X a) hU y z).mpr hyz))⟩

/-- Actual normalized models modulo actual integral-order equivariant
isomorphisms with their original scalar polarization and level equations. -/
def TateNormalizedCMOrdinaryIsoClass (X : Bases) (a : HarrisGeometricPoint X.obj.left)
    (U : HarrisLevel D) (hU : (lev U).toSubgroup ≤ harrisIntegralAdeleStabilizer D C) :=
  Quotient (tateNormalizedCMOrdinarySetoid D C P compatibility h htor X a U hU)

local notation "OClassesAt" X:max a:max =>
  TateNormalizedCMOrdinaryIsoClass D C P compatibility h htor X a

/-- Pass an actual normalized model to its ordinary class. -/
def tateNormalizedCMOrdinaryClassOf (X : Bases) (a : HarrisGeometricPoint X.obj.left)
    (U : HarrisLevel D) (hU : (lev U).toSubgroup ≤ harrisIntegralAdeleStabilizer D C)
    (x : (NRepAt X a) U) : (OClassesAt X a) U hU := Quotient.mk _ x

local notation "omk" X:max a:max =>
  tateNormalizedCMOrdinaryClassOf D C P compatibility h htor X a

/-- Ordinary classes identify precisely the actual-isomorphism relation. -/
theorem tateNormalizedCMOrdinaryClassOf_eq_iff (X : Bases)
    (a : HarrisGeometricPoint X.obj.left) (U : HarrisLevel D)
    (hU : (lev U).toSubgroup ≤ harrisIntegralAdeleStabilizer D C)
    (x y : (NRepAt X a) U) :
    (omk X a) U hU x = (omk X a) U hU y ↔ (ordinaryRel X a) x y := Quotient.eq

/-- The identity on actual normalized models compares the ordinary and unchanged
rational-isogeny quotients in both directions. -/
def tateNormalizedCMOrdinaryClassEquiv (X : Bases)
    (a : HarrisGeometricPoint X.obj.left) (U : HarrisLevel D)
    (hU : (lev U).toSubgroup ≤ harrisIntegralAdeleStabilizer D C) :
    (OClassesAt X a) U hU ≃ (NClassesAt X a) U where
  toFun := Quotient.map id (fun x y hxy => ((relIff X a) hU x y).mpr hxy)
  invFun := Quotient.map id (fun x y hxy => ((relIff X a) hU x y).mp hxy)
  left_inv q := by
    refine Quotient.inductionOn q ?_
    intro x
    rfl
  right_inv q := by
    refine Quotient.inductionOn q ?_
    intro x
    rfl

local notation "ordinaryEquiv" =>
  tateNormalizedCMOrdinaryClassEquiv D C P compatibility h htor

@[simp] theorem tateNormalizedCMOrdinaryClassEquiv_classOf (X : Bases)
    (a : HarrisGeometricPoint X.obj.left) (U : HarrisLevel D)
    (hU : (lev U).toSubgroup ≤ harrisIntegralAdeleStabilizer D C)
    (x : (NRepAt X a) U) :
    ordinaryEquiv X a U hU ((omk X a) U hU x) =
      tateNormalizedCMClassOf D C P X compatibility h a.hom a.finiteFibers htor x := rfl

/-- Forgetting an ordinary class returns its identical original CM class. -/
def tateNormalizedCMOrdinaryForget (X : Bases) (a : HarrisGeometricPoint X.obj.left)
    (U : HarrisLevel D) (hU : (lev U).toSubgroup ≤ harrisIntegralAdeleStabilizer D C) :=
  (nForget X a) ∘ ordinaryEquiv X a U hU

local notation "forget" => tateNormalizedCMOrdinaryForget D C P compatibility h htor

@[simp] theorem tateNormalizedCMOrdinaryForget_classOf (X : Bases)
    (a : HarrisGeometricPoint X.obj.left) (U : HarrisLevel D)
    (hU : (lev U).toSubgroup ≤ harrisIntegralAdeleStabilizer D C)
    (x : (NRepAt X a) U) :
    forget X a U hU ((omk X a) U hU x) = (repClassAt X a) x := rfl

/-- Ordinary normalization introduces no duplicate original classes. -/
theorem tateNormalizedCMOrdinaryForget_injective (X : Bases)
    (a : HarrisGeometricPoint X.obj.left) (U : HarrisLevel D)
    (hU : (lev U).toSubgroup ≤ harrisIntegralAdeleStabilizer D C) :
    Function.Injective (forget X a U hU) :=
  (tateNormalizedCMForget_injective D C P X compatibility h a.hom a.finiteFibers htor).comp
    (ordinaryEquiv X a U hU).injective

section Points

variable (X : AdmissibleCMBaseCategory D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality)
  (a b c : HarrisGeometricPoint X.obj.left)

/-- The existing actual representative point transport preserves ordinary
isomorphism, with the same polarization scalar and original level condition. -/
theorem tateNormalizedCMOrdinaryRelated_pointMap
    (path : fiberFunctor a.hom a.finiteFibers ≅ fiberFunctor b.hom b.finiteFibers)
    (U : HarrisLevel D) (hU : (lev U).toSubgroup ≤ harrisIntegralAdeleStabilizer D C)
    (x y : (NRepAt X a) U) (hxy : (ordinaryRel X a) x y) :
    (ordinaryRel X b)
      (tateNormalizedCMRepresentativePointMap D C P X compatibility h htor path U x)
      (tateNormalizedCMRepresentativePointMap D C P X compatibility h htor path U y) :=
  ((relIff X b) hU _ _).mp
    (tateNormalizedCMRelated_pointMap D C P X compatibility h htor path U x y
      (((relIff X a) hU x y).mpr hxy))

/-- Ordinary point transport descends the actual representative map, without
choosing an inverse to a forgetful comparison. -/
def tateNormalizedCMOrdinaryClassPointMap
    (path : fiberFunctor a.hom a.finiteFibers ≅ fiberFunctor b.hom b.finiteFibers)
    (U : HarrisLevel D) (hU : (lev U).toSubgroup ≤ harrisIntegralAdeleStabilizer D C) :
    (OClassesAt X a) U hU → (OClassesAt X b) U hU :=
  Quotient.map (tateNormalizedCMRepresentativePointMap D C P X compatibility h htor path U)
    (tateNormalizedCMOrdinaryRelated_pointMap D C P compatibility h htor X a b path U hU)

local notation "move" => tateNormalizedCMOrdinaryClassPointMap D C P compatibility h htor

/-- The ordinary and unchanged normalized point maps commute on the same models. -/
@[simp] theorem tateNormalizedCMOrdinaryClassEquiv_pointMap
    (path : fiberFunctor a.hom a.finiteFibers ≅ fiberFunctor b.hom b.finiteFibers)
    (U : HarrisLevel D) (hU : (lev U).toSubgroup ≤ harrisIntegralAdeleStabilizer D C)
    (q : (OClassesAt X a) U hU) :
    ordinaryEquiv X b U hU (move X a b path U hU q) =
      (NMove X a b path) U (ordinaryEquiv X a U hU q) := by
  refine Quotient.inductionOn q ?_
  intro x
  rfl

/-- Reversing the original path is the inverse on ordinary classes. -/
def tateNormalizedCMOrdinaryClassPointEquiv
    (path : fiberFunctor a.hom a.finiteFibers ≅ fiberFunctor b.hom b.finiteFibers)
    (U : HarrisLevel D) (hU : (lev U).toSubgroup ≤ harrisIntegralAdeleStabilizer D C) :
    (OClassesAt X a) U hU ≃ (OClassesAt X b) U hU where
  toFun := move X a b path U hU
  invFun := move X b a path.symm U hU
  left_inv q := by
    apply (ordinaryEquiv X a U hU).injective
    simp only [tateNormalizedCMOrdinaryClassEquiv_pointMap]
    exact (tateNormalizedCMClassPointEquiv D C P X compatibility h htor path U).left_inv _
  right_inv q := by
    apply (ordinaryEquiv X b U hU).injective
    simp only [tateNormalizedCMOrdinaryClassEquiv_pointMap]
    exact (tateNormalizedCMClassPointEquiv D C P X compatibility h htor path U).right_inv _

/-- Ordinary point transport is independent of the chosen geometric path. -/
theorem tateNormalizedCMOrdinaryClassPointMap_path_independent
    (path path' : fiberFunctor a.hom a.finiteFibers ≅ fiberFunctor b.hom b.finiteFibers)
    (U : HarrisLevel D) (hU : (lev U).toSubgroup ≤ harrisIntegralAdeleStabilizer D C) :
    move X a b path U hU = move X a b path' U hU := by
  funext q
  apply (ordinaryEquiv X b U hU).injective
  simp only [tateNormalizedCMOrdinaryClassEquiv_pointMap]
  exact congrFun (tateNormalizedCMClassPointMap_path_independent D C P X
    compatibility h htor path path' U) _

@[simp] theorem tateNormalizedCMOrdinaryClassPointMap_refl
    (U : HarrisLevel D) (hU : (lev U).toSubgroup ≤ harrisIntegralAdeleStabilizer D C)
    (q : (OClassesAt X a) U hU) :
    move X a a (Iso.refl _) U hU q = q := by
  apply (ordinaryEquiv X a U hU).injective
  rw [tateNormalizedCMOrdinaryClassEquiv_pointMap]
  exact tateNormalizedCMClassPointMap_refl D C P X compatibility h htor U _

/-- Composing actual geometric paths composes the ordinary quotient maps. -/
theorem tateNormalizedCMOrdinaryClassPointMap_trans
    (path : fiberFunctor a.hom a.finiteFibers ≅ fiberFunctor b.hom b.finiteFibers)
    (path' : fiberFunctor b.hom b.finiteFibers ≅ fiberFunctor c.hom c.finiteFibers)
    (U : HarrisLevel D) (hU : (lev U).toSubgroup ≤ harrisIntegralAdeleStabilizer D C)
    (q : (OClassesAt X a) U hU) :
    move X a c (path ≪≫ path') U hU q = move X b c path' U hU (move X a b path U hU q) := by
  apply (ordinaryEquiv X c U hU).injective
  simp only [tateNormalizedCMOrdinaryClassEquiv_pointMap]
  exact tateNormalizedCMClassPointMap_trans D C P X compatibility h htor path path' U _

end Points

section Pullback

variable (dualityNaturality : DualAbelianBaseChangeNaturalityStatement.{0})
  (polarizationStability : PolarizationBaseChangeStatement.{0})
  {X Y : AdmissibleCMBaseCategory D C P.preservation P.composition
    P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality}
  (f : Y ⟶ X) (a : HarrisGeometricPoint Y.obj.left)

local notation "pullRep" => tateNormalizedCMRepresentativeBaseChange D C P
  dualityNaturality polarizationStability compatibility h htor
local notation "pullN" => tateNormalizedCMClassBaseChange D C P
  dualityNaturality polarizationStability compatibility h htor

/-- Actual normalized base change preserves the ordinary actual-isomorphism
relation on the very representatives pulled back by the existing construction. -/
theorem tateNormalizedCMOrdinaryRelated_baseChange
    (U : HarrisLevel D) (hU : (lev U).toSubgroup ≤ harrisIntegralAdeleStabilizer D C)
    (x y : (NRepAt X (a.comp f.hom.left)) U)
    (hxy : (ordinaryRel X (a.comp f.hom.left)) x y) :
    (ordinaryRel Y a) (pullRep f a U x) (pullRep f a U y) :=
  ((relIff Y a) hU _ _).mp
    (tateNormalizedCMRelated_baseChange D C P dualityNaturality polarizationStability
      compatibility h htor f a U x y (((relIff X (a.comp f.hom.left)) hU x y).mpr hxy))

/-- Ordinary base change is the quotient of the actual normalized model pullback. -/
def tateNormalizedCMOrdinaryClassBaseChange
    (U : HarrisLevel D) (hU : (lev U).toSubgroup ≤ harrisIntegralAdeleStabilizer D C) :
    (OClassesAt X (a.comp f.hom.left)) U hU → (OClassesAt Y a) U hU :=
  Quotient.map (pullRep f a U)
    (tateNormalizedCMOrdinaryRelated_baseChange D C P compatibility h htor
      dualityNaturality polarizationStability f a U hU)

/-- The ordinary and unchanged normalized base-change maps commute literally
on classes of the same actual pulled-back models. -/
@[simp] theorem tateNormalizedCMOrdinaryClassEquiv_baseChange
    (U : HarrisLevel D) (hU : (lev U).toSubgroup ≤ harrisIntegralAdeleStabilizer D C)
    (q : (OClassesAt X (a.comp f.hom.left)) U hU) :
    ordinaryEquiv Y a U hU
      (tateNormalizedCMOrdinaryClassBaseChange D C P compatibility h htor
        dualityNaturality polarizationStability f a U hU q) =
      pullN f a U (ordinaryEquiv X (a.comp f.hom.left) U hU q) := by
  refine Quotient.inductionOn q ?_
  intro x
  rfl

end Pullback

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

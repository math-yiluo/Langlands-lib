import Langlands.Shimura.PEL.HarrisTaylorCMTateFunctoriality

/-! # Compatible geometric families of full Tate-normalized CM classes -/

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
open GroupScheme.Tate (Index)

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
local notation "NClassesAt" X:max a:max =>
  TateNormalizedCMIsoClass D C P X compatibility h (a).hom (a).finiteFibers htor
local notation "forgetAt" X:max a:max =>
  tateNormalizedCMForget D C P X compatibility h (a).hom (a).finiteFibers htor
local notation "originalMove" X:max a:max b:max =>
  geometricClassComparison D C P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability P.square P.universality
    (X).obj.hom compatibility h htor (X).property.torsionUnits
    (X).property.pairAdditivity a b
local notation "originalTower" X:max =>
  unpointedClassTower D C P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability P.square P.universality
    compatibility h htor X

/-- Canonical comparison of actual normalized quotient classes at geometric points. -/
def tateNormalizedCMGeometricComparison (X : Bases)
    (a b : HarrisGeometricPoint X.obj.left) (U : HarrisLevel D) :
    (NClassesAt X a) U ≃ (NClassesAt X b) U :=
  tateNormalizedCMClassGeometricPointEquiv D C P X compatibility h htor
    (s := a.hom) (t := b.hom) (hs := a.finiteFibers) (ht := b.finiteFibers) U

local notation "move" => tateNormalizedCMGeometricComparison D C P compatibility h htor

/-- The canonical normalized comparison forgets to the original canonical comparison. -/
@[simp] theorem tateNormalizedCMForget_geometricComparison (X : Bases)
    (a b : HarrisGeometricPoint X.obj.left) (U : HarrisLevel D)
    (q : (NClassesAt X a) U) :
    (forgetAt X b) (move X a b U q) =
      (originalMove X a b).hom.app U ((forgetAt X a) q) :=
  tateNormalizedCMForget_pointMap D C P X compatibility h htor _ U q

@[simp] theorem tateNormalizedCMGeometricComparison_refl (X : Bases)
    (a : HarrisGeometricPoint X.obj.left) (U : HarrisLevel D)
    (q : (NClassesAt X a) U) : move X a a U q = q := by
  apply tateNormalizedCMForget_injective D C P X compatibility h a.hom a.finiteFibers htor
  rw [tateNormalizedCMForget_geometricComparison]
  exact congrArg (fun k => k.hom.app U ((forgetAt X a) q))
    (geometricClassComparison_refl D C P.preservation P.composition P.unitCoherence
      P.associativity P.comparison P.symmetry P.stability P.square P.universality
      X.obj.hom compatibility h htor X.property.torsionUnits X.property.pairAdditivity a)

/-- The canonical normalized comparisons compose across independent point fields. -/
theorem tateNormalizedCMGeometricComparison_trans (X : Bases)
    (a b c : HarrisGeometricPoint X.obj.left) (U : HarrisLevel D)
    (q : (NClassesAt X a) U) :
    move X a c U q = move X b c U (move X a b U q) := by
  apply tateNormalizedCMForget_injective D C P X compatibility h c.hom c.finiteFibers htor
  simp only [tateNormalizedCMForget_geometricComparison]
  exact congrArg (fun k => k.hom.app U ((forgetAt X a) q))
    (geometricClassComparison_trans D C P.preservation P.composition P.unitCoherence
      P.associativity P.comparison P.symmetry P.stability P.square P.universality
      X.obj.hom compatibility h htor X.property.torsionUnits X.property.pairAdditivity a b c)

/-- Actual normalized quotient classes compatible at every pair of geometric points. -/
def TateNormalizedCMGeometricFamily (X : Bases) (U : HarrisLevel D) : Type 1 :=
  {x : (a : HarrisGeometricPoint X.obj.left) → (NClassesAt X a) U //
    ∀ a b, move X a b U (x a) = x b}

local notation "Family" => TateNormalizedCMGeometricFamily D C P compatibility h htor

/-- Forget the actual normalized models pointwise into the original unpointed CM value. -/
def tateNormalizedCMFamilyForget (X : Bases) (U : HarrisLevel D) :
    Family X U → (originalTower X).obj U :=
  fun x => ⟨fun a => (forgetAt X a) (x.val a), by
    intro a b
    rw [← tateNormalizedCMForget_geometricComparison, x.property a b]⟩

local notation "forgetFamily" => tateNormalizedCMFamilyForget D C P compatibility h htor

/-- Equality is reflected without assuming existence of normalized models. -/
theorem tateNormalizedCMFamilyForget_injective (X : Bases) (U : HarrisLevel D) :
    Function.Injective (forgetFamily X U) := by
  intro x y hxy
  apply Subtype.ext
  funext a
  apply tateNormalizedCMForget_injective D C P X compatibility h a.hom a.finiteFibers htor
  exact congrArg (fun z => z.val a) hxy

/-- Extend a normalized quotient class by actual canonical point comparisons. -/
def tateNormalizedCMGeometricFamilyExtension (X : Bases)
    (a : HarrisGeometricPoint X.obj.left) (U : HarrisLevel D)
    (q : (NClassesAt X a) U) : Family X U :=
  ⟨fun b => move X a b U q, by
    intro b c
    exact (tateNormalizedCMGeometricComparison_trans D C P compatibility h htor
      X a b c U q).symm⟩

local notation "extend" => tateNormalizedCMGeometricFamilyExtension D C P compatibility h htor

/-- Evaluation at any actual geometric point is an equivalence on normalized families. -/
def tateNormalizedCMGeometricFamilyEvaluationEquiv (X : Bases)
    (a : HarrisGeometricPoint X.obj.left) (U : HarrisLevel D) :
    Family X U ≃ (NClassesAt X a) U where
  toFun x := x.val a
  invFun := extend X a U
  left_inv x := by
    apply Subtype.ext
    funext b
    exact x.property a b
  right_inv q := tateNormalizedCMGeometricComparison_refl D C P compatibility h htor X a U q

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- Every actual geometric point of a CM-field base has characteristic zero. -/
theorem harrisCMGeometricPoint_charZero (X : Bases)
    (a : HarrisGeometricPoint X.obj.left) : CharZero a.Ω := by
  let φ : F →+* a.Ω := ((Scheme.ΓSpecIso (.of F)).inv ≫
    (a.hom ≫ X.obj.hom).appTop ≫ (Scheme.ΓSpecIso (.of a.Ω)).hom).hom
  exact charZero_of_injective_ringHom φ.injective

section Existence

variable (fibreAmple : ProperFibreAmpleAffineOpenStatement.{0})
  (realize : Tate.CommensurableInvariantLatticeRealizationStatement.{0})

include fibreAmple realize in
/-- At a source-stabilizing level, every original unpointed CM value has an actual
normalized family under the explicit two generic geometric prerequisites. -/
theorem tateNormalizedCMFamilyForget_surjective (X : Bases) (U : HarrisLevel D)
    (hU : ((hodgeLevelFunctor D C).obj U).toSubgroup ≤ harrisIntegralAdeleStabilizer D C) :
    Function.Surjective (forgetFamily X U) := by
  intro x
  let a : HarrisGeometricPoint X.obj.left := Classical.arbitrary _
  let := harrisCMGeometricPoint_charZero D C P X a
  obtain ⟨q, hq⟩ := tateNormalizedCMForget_surjective D C P X compatibility h
    a.hom a.finiteFibers htor fibreAmple realize hU (x.val a)
  refine ⟨extend X a U q, ?_⟩
  apply Subtype.ext
  funext b
  change (forgetAt X b) (move X a b U q) = x.val b
  rw [tateNormalizedCMForget_geometricComparison, hq]
  exact x.property a b

/-- The comparison uses the literal pointwise forgetful map as its forward map. -/
def tateNormalizedCMGeometricFamilyEquiv (X : Bases) (U : HarrisLevel D)
    (hU : ((hodgeLevelFunctor D C).obj U).toSubgroup ≤ harrisIntegralAdeleStabilizer D C) :
    Family X U ≃ (originalTower X).obj U :=
  Equiv.ofBijective (forgetFamily X U)
    ⟨tateNormalizedCMFamilyForget_injective D C P compatibility h htor X U,
      tateNormalizedCMFamilyForget_surjective D C P compatibility h htor
        fibreAmple realize X U hU⟩

end Existence

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

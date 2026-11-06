import Langlands.Shimura.PEL.HarrisTaylorCMTateNormalization
import Langlands.AbelianScheme.PolarizedFiniteLevel.PolarizationFibreAffine

/-! # Full Tate-normalized representatives of the original CM class set -/

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
  (Z : AdmissibleCMBaseCategory D C P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability P.square P.universality)
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  {Ω : Type} [Field Ω] (s : Spec (.of Ω) ⟶ Z.obj.left)
  (hs : ∀ Y : Cover Z.obj.left, Finite (Fiber s Y))
  (htor : TorsionFiniteEtaleStatement.{0})

local notation "hΦ" => isCMSection_harrisCMSection E (algebraMap L F) τ₀
local notation "NRep" => TateNormalizedCMRepresentative D C P Z compatibility h s hs htor
local notation "repClass" => integralCMRepresentativeClass D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
  Z.obj.hom compatibility h s hs htor Z.property.torsionUnits Z.property.pairAdditivity
local notation "Classes" => HarrisNumericalWeilLevel.IsoClass D C hΦ P.preservation
  P.composition P.unitCoherence P.associativity P.comparison P.symmetry P.stability
  P.square P.universality (D.harrisTaylorReflexStructure C Z.obj.hom) compatibility h
  s hs htor Z.property.torsionUnits Z.property.pairAdditivity L Z.obj.hom
local notation "IRelated" => IntegralCMRelated D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
  Z.obj.hom compatibility h s hs htor Z.property.torsionUnits Z.property.pairAdditivity
local notation "relIff" => integralCMRelated_iff_class_eq D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
  Z.obj.hom compatibility h s hs htor Z.property.torsionUnits Z.property.pairAdditivity
local notation "IClasses" => IntegralCMIsoClass D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
  Z.obj.hom compatibility h s hs htor Z.property.torsionUnits Z.property.pairAdditivity
local notation "imk" => integralCMClassOf D C P.preservation P.composition P.unitCoherence
  P.associativity P.comparison P.symmetry P.stability P.square P.universality Z.obj.hom
  compatibility h s hs htor Z.property.torsionUnits Z.property.pairAdditivity
local notation "iforget" => integralCMForget D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
  Z.obj.hom compatibility h s hs htor Z.property.torsionUnits Z.property.pairAdditivity

/-- Forget full Tate normalization and the actual order action into the original CM class. -/
def tateNormalizedCMRepresentativeClass {U : HarrisLevel D} (x : NRep U) : Classes U :=
  repClass x.toIntegralCMRepresentative

local notation "nrepClass" => tateNormalizedCMRepresentativeClass D C P Z
  compatibility h s hs htor

/-- Full Tate-normalized representatives retain the original rational-isogeny relation,
expressed by the existing exact integral witnesses. -/
def TateNormalizedCMRelated {U : HarrisLevel D} (x y : NRep U) : Prop :=
  IRelated x.toIntegralCMRepresentative y.toIntegralCMRepresentative

local notation "Related" => TateNormalizedCMRelated D C P Z compatibility h s hs htor

/-- Two normalized models are related exactly when their original CM classes agree. -/
theorem tateNormalizedCMRelated_iff_class_eq {U : HarrisLevel D} (x y : NRep U) :
    Related x y ↔ nrepClass x = nrepClass y :=
  relIff x.toIntegralCMRepresentative y.toIntegralCMRepresentative

local notation "nrelIff" => tateNormalizedCMRelated_iff_class_eq D C P Z
  compatibility h s hs htor

/-- The unchanged rational-isogeny relation is an equivalence on normalized models. -/
def tateNormalizedCMSetoid (U : HarrisLevel D) : Setoid (NRep U) where
  r := Related
  iseqv := ⟨fun x => (nrelIff x x).mpr rfl,
    fun {x y} hxy => (nrelIff y x).mpr ((nrelIff x y).mp hxy).symm,
    fun {x y z} hxy hyz =>
      (nrelIff x z).mpr (((nrelIff x y).mp hxy).trans ((nrelIff y z).mp hyz))⟩

local notation "nsetoid" => tateNormalizedCMSetoid D C P Z compatibility h s hs htor

/-- Actual full Tate-normalized models modulo the original rational-isogeny relation. -/
def TateNormalizedCMIsoClass (U : HarrisLevel D) := Quotient (nsetoid U)

local notation "NClasses" => TateNormalizedCMIsoClass D C P Z compatibility h s hs htor

/-- Form the normalized model's class without choosing an isogeny or a frame. -/
def tateNormalizedCMClassOf {U : HarrisLevel D} (x : NRep U) : NClasses U :=
  Quotient.mk _ x

local notation "nmk" => tateNormalizedCMClassOf D C P Z compatibility h s hs htor

/-- The quotient identifies precisely the original rational-isogeny witnesses. -/
theorem tateNormalizedCMClassOf_eq_iff {U : HarrisLevel D} (x y : NRep U) :
    nmk x = nmk y ↔ Related x y := Quotient.eq

/-- Forgetting descends to the original CM class set. -/
def tateNormalizedCMForget {U : HarrisLevel D} : NClasses U → Classes U :=
  Quotient.lift nrepClass (fun x y hxy => (nrelIff x y).mp hxy)

local notation "forget" => tateNormalizedCMForget D C P Z compatibility h s hs htor

@[simp] theorem tateNormalizedCMForget_classOf {U : HarrisLevel D} (x : NRep U) :
    forget (nmk x) = nrepClass x := rfl

/-- Full Tate normalization produces neither duplicate classes nor new identifications. -/
theorem tateNormalizedCMForget_injective {U : HarrisLevel D} :
    Function.Injective (forget : NClasses U → Classes U) := by
  intro x y
  refine Quotient.inductionOn₂ x y ?_
  intro a b hab
  exact Quotient.sound ((nrelIff a b).mpr hab)

/-- Forget only Tate normalization, retaining the original integral-witness quotient. -/
def tateNormalizedCMToIntegralClass {U : HarrisLevel D} : NClasses U → IClasses U :=
  Quotient.map (fun x => x.toIntegralCMRepresentative) (fun _ _ hxy => hxy)

local notation "toIntegral" => tateNormalizedCMToIntegralClass D C P Z
  compatibility h s hs htor

@[simp] theorem tateNormalizedCMToIntegralClass_classOf {U : HarrisLevel D}
    (x : NRep U) :
    toIntegral (nmk x) = imk x.toIntegralCMRepresentative := rfl

/-- Both forgetful routes return the identical original CM class. -/
@[simp] theorem tateNormalizedCMForget_toIntegral {U : HarrisLevel D} (q : NClasses U) :
    iforget (toIntegral q) = forget q := by
  refine Quotient.inductionOn q ?_
  intro x
  rfl

/-- Forgetting only Tate normalization is also injective. -/
theorem tateNormalizedCMToIntegralClass_injective {U : HarrisLevel D} :
    Function.Injective (toIntegral : NClasses U → IClasses U) := by
  intro x y hxy
  apply tateNormalizedCMForget_injective D C P Z compatibility h s hs htor
  simpa only [tateNormalizedCMForget_toIntegral] using congrArg iforget hxy

section Existence

variable [IsAlgClosed Ω] [CharZero Ω]
  (fibreAmple : ProperFibreAmpleAffineOpenStatement.{0})
  (realize : Tate.CommensurableInvariantLatticeRealizationStatement.{0})

local notation "jointProof" => determinantDimensionCondition_iff D C P.preservation
  P.composition P.unitCoherence P.associativity P.comparison P.symmetry P.stability
  P.square P.universality Z.obj.hom

include fibreAmple realize in
/-- Every original class at a source-stabilizing level has a full Tate-normalized
representative. Its source fibre-affineness follows from its actual polarization. -/
theorem tateNormalizedCMRepresentative_exists {U : HarrisLevel D}
    (hU : ((hodgeLevelFunctor D C).obj U).toSubgroup ≤ harrisIntegralAdeleStabilizer D C)
    (q : Classes U) : ∃ x : NRep U, nrepClass x = q := by
  let := auxiliaryStarRing D C
  obtain ⟨x, hx, hn, rfl⟩ := HarrisNumericalWeilLevel.classOf_surjective D C hΦ
    P.preservation P.composition P.unitCoherence P.associativity P.comparison P.symmetry
    P.stability P.square P.universality (D.harrisTaylorReflexStructure C Z.obj.hom)
    compatibility h s hs htor Z.property.torsionUnits Z.property.pairAdditivity L Z.obj.hom q
  have hc := (jointProof x.1).mpr ⟨hx, hn⟩
  exact exists_tateNormalizedCMRepresentative D C P Z compatibility h s hs htor
    x hc hU realize
    (DualWitness.forall_finset_fibre_affine P fibreAmple
      (PolarizedWeilLevel.PolarizedAction.dualWitness P x.1)
      x.1.polarization x.1.isPolarization)

include fibreAmple realize in
/-- Every original class is covered by the normalized quotient under the two explicit
generic geometric prerequisites and source-stabilizer containment. -/
theorem tateNormalizedCMForget_surjective {U : HarrisLevel D}
    (hU : ((hodgeLevelFunctor D C).obj U).toSubgroup ≤ harrisIntegralAdeleStabilizer D C) :
    Function.Surjective (forget : NClasses U → Classes U) := by
  intro q
  obtain ⟨x, hx⟩ := tateNormalizedCMRepresentative_exists D C P Z compatibility h
    s hs htor fibreAmple realize hU q
  exact ⟨nmk x, hx⟩

/-- The equivalence uses the literal forgetful map; its inverse's model choices
disappear in the unchanged rational-isogeny quotient. -/
def tateNormalizedCMClassEquiv (U : HarrisLevel D)
    (hU : ((hodgeLevelFunctor D C).obj U).toSubgroup ≤ harrisIntegralAdeleStabilizer D C) :
    NClasses U ≃ Classes U :=
  Equiv.ofBijective forget
    ⟨tateNormalizedCMForget_injective D C P Z compatibility h s hs htor,
      tateNormalizedCMForget_surjective D C P Z compatibility h s hs htor
        fibreAmple realize hU⟩

@[simp] theorem tateNormalizedCMClassEquiv_apply (U : HarrisLevel D)
    (hU : ((hodgeLevelFunctor D C).obj U).toSubgroup ≤ harrisIntegralAdeleStabilizer D C)
    (q : NClasses U) :
    tateNormalizedCMClassEquiv D C P Z compatibility h s hs htor
      fibreAmple realize U hU q = forget q := rfl

include fibreAmple realize in
/-- The same normalization covers every class of representatives with integral action. -/
theorem tateNormalizedCMToIntegralClass_surjective {U : HarrisLevel D}
    (hU : ((hodgeLevelFunctor D C).obj U).toSubgroup ≤ harrisIntegralAdeleStabilizer D C) :
    Function.Surjective (toIntegral : NClasses U → IClasses U) := by
  intro q
  obtain ⟨r, hr⟩ := tateNormalizedCMForget_surjective D C P Z compatibility h
    s hs htor fibreAmple realize hU (iforget q)
  refine ⟨r, ?_⟩
  apply integralCMForget_injective D C P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability P.square P.universality
    Z.obj.hom compatibility h s hs htor Z.property.torsionUnits Z.property.pairAdditivity
  exact (tateNormalizedCMForget_toIntegral D C P Z compatibility h s hs htor r).trans hr

end Existence

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

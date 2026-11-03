import Langlands.Shimura.PEL.HarrisTaylorCMOrderModel

/-! # Integral representatives of every normalized Harris CM class -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

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
  (fibreAmple : ProperFibreAmpleAffineOpenStatement.{0})
  (htor : TorsionFiniteEtaleStatement.{0})
  (Z : AdmissibleCMBaseCategory D C P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability P.square P.universality)
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  {Ω : Type} [Field Ω] (s : Spec (.of Ω) ⟶ Z.obj.left)
  (hs : ∀ Y : Cover Z.obj.left, Finite (Fiber s Y))

local notation "hΦ" => isCMSection_harrisCMSection E (algebraMap L F) τ₀
local notation "Data" => HarrisLevelData D C P.preservation P.composition P.unitCoherence
  P.associativity P.comparison P.symmetry P.stability P.square P.universality compatibility h
  s hs htor Z.property.torsionUnits
local notation "Rep" => IntegralCMRepresentative D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
  Z.obj.hom compatibility h s hs htor Z.property.torsionUnits
local notation "jointProof" => determinantDimensionCondition_iff D C P.preservation
  P.composition P.unitCoherence P.associativity P.comparison P.symmetry P.stability
  P.square P.universality Z.obj.hom
local notation "mkClass" => HarrisNumericalWeilLevel.classOf D C hΦ P.preservation
  P.composition P.unitCoherence P.associativity P.comparison P.symmetry P.stability
  P.square P.universality (D.harrisTaylorReflexStructure C Z.obj.hom) compatibility h
  s hs htor Z.property.torsionUnits Z.property.pairAdditivity L Z.obj.hom
local notation "repClass" => integralCMRepresentativeClass D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
  Z.obj.hom compatibility h s hs htor Z.property.torsionUnits Z.property.pairAdditivity
local notation "transport" => PolarizedWeilLevel.levelIso P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
  compatibility h A (D.harrisHodgePELForm C) s hs htor Z.property.torsionUnits
  Z.property.pairAdditivity
local notation "model" => cmPolarizedOrderModel D C P fibreAmple htor Z
local notation "modelIso" => cmPolarizedOrderModelIso D C P fibreAmple htor Z
local notation "modelQ" => cmPolarizedOrderModelMultiplier D C P fibreAmple htor Z
local notation "modelMult" => cmPolarizedOrderModel_multiple D C P fibreAmple htor Z

/-- Transport the actual level orbit to the constructed integral polarized model. -/
def cmIntegralRepresentative {U : HarrisLevel D} (x : Data U)
    (hx : letI := auxiliaryStarRing D C
      D.HarrisTaylorCMDeterminantDimensionCondition C Z.obj.hom
        x.1.actionObj.abelianScheme x.1.actionObj.action) : Rep U := by
  letI := auxiliaryStarRing D C
  refine ⟨⟨model x.1, transport x.1 (model x.1) ((hodgeLevelFunctor D C).obj U)
      (modelQ x.1) (modelIso x.1) (modelMult x.1) x.2⟩, ?_,
    cmPolarizedOrderModelRestriction D C P fibreAmple htor Z x.1⟩
  exact (cmPolarizedOrderModel_condition_iff D C P fibreAmple htor Z x.1).mp hx

local notation "integralize" => cmIntegralRepresentative D C P fibreAmple htor Z
  compatibility h s hs

/-- The constructed integral representative gives the exact original normalized class. -/
theorem cmIntegralRepresentativeClass_eq {U : HarrisLevel D} (x : Data U)
    (hx : letI := auxiliaryStarRing D C
      D.HarrisTaylorCMDeterminantDimensionCondition C Z.obj.hom
        x.1.actionObj.abelianScheme x.1.actionObj.action) :
    repClass (integralize x hx) =
      mkClass x ((jointProof x.1).mp hx).1 ((jointProof x.1).mp hx).2 := by
  let := auxiliaryStarRing D C
  symm
  apply (HarrisNumericalWeilLevel.classOf_eq_iff D C hΦ P.preservation P.composition
    P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
    (D.harrisTaylorReflexStructure C Z.obj.hom) compatibility h s hs htor
    Z.property.torsionUnits Z.property.pairAdditivity L Z.obj.hom x (integralize x hx).data
    ((jointProof x.1).mp hx).1
    ((jointProof (integralize x hx).data.1).mp (integralize x hx).condition).1
    ((jointProof x.1).mp hx).2
    ((jointProof (integralize x hx).data.1).mp (integralize x hx).condition).2).mpr
  exact ⟨modelQ x.1, modelIso x.1, modelMult x.1, rfl⟩

local notation "Classes" => HarrisNumericalWeilLevel.IsoClass D C hΦ P.preservation
  P.composition P.unitCoherence P.associativity P.comparison P.symmetry P.stability
  P.square P.universality (D.harrisTaylorReflexStructure C Z.obj.hom) compatibility h
  s hs htor Z.property.torsionUnits Z.property.pairAdditivity L Z.obj.hom
local notation "imageCondition" => IntegralCMClassCondition D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
  Z.obj.hom compatibility h s hs htor Z.property.torsionUnits Z.property.pairAdditivity

include fibreAmple in
/-- Every normalized class over the existing admissible CM base has an actual
integral representative, under the explicit generic fibre-ampleness premise. -/
theorem integralCMClassCondition_all {U : HarrisLevel D} (q : Classes U) :
    imageCondition q := by
  let := auxiliaryStarRing D C
  obtain ⟨x, hx, hn, rfl⟩ := HarrisNumericalWeilLevel.classOf_surjective D C hΦ
    P.preservation P.composition P.unitCoherence P.associativity P.comparison P.symmetry
    P.stability P.square P.universality (D.harrisTaylorReflexStructure C Z.obj.hom)
    compatibility h s hs htor Z.property.torsionUnits Z.property.pairAdditivity L Z.obj.hom q
  have hc := (jointProof x.1).mpr ⟨hx, hn⟩
  exact ⟨integralize x hc, cmIntegralRepresentativeClass_eq D C P fibreAmple htor Z
    compatibility h s hs x hc⟩

local notation "IClasses" => IntegralCMIsoClass D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
  Z.obj.hom compatibility h s hs htor Z.property.torsionUnits Z.property.pairAdditivity
local notation "forget" => integralCMForget D C P.preservation P.composition P.unitCoherence
  P.associativity P.comparison P.symmetry P.stability P.square P.universality Z.obj.hom
  compatibility h s hs htor Z.property.torsionUnits Z.property.pairAdditivity
local notation "imk" => integralCMClassOf D C P.preservation P.composition P.unitCoherence
  P.associativity P.comparison P.symmetry P.stability P.square P.universality Z.obj.hom
  compatibility h s hs htor Z.property.torsionUnits Z.property.pairAdditivity
local notation "itower" => integralCMClassTower D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
  Z.obj.hom compatibility h s hs htor Z.property.torsionUnits Z.property.pairAdditivity
local notation "tower" => HarrisNumericalWeilLevel.isoClassTower D C hΦ P.preservation
  P.composition P.unitCoherence P.associativity P.comparison P.symmetry P.stability
  P.square P.universality (D.harrisTaylorReflexStructure C Z.obj.hom) compatibility h
  s hs htor Z.property.torsionUnits Z.property.pairAdditivity L Z.obj.hom

include fibreAmple in
/-- Forgetting integral representatives covers every existing normalized class. -/
theorem integralCMForget_surjective {U : HarrisLevel D} :
    Function.Surjective (forget : IClasses U → Classes U) := by
  intro q
  obtain ⟨x, hx⟩ := integralCMClassCondition_all D C P fibreAmple htor Z
    compatibility h s hs q
  exact ⟨imk x, hx⟩

include fibreAmple in
/-- The original forgetful function is an equivalence of the exact class sets. -/
def integralCMClassEquiv (U : HarrisLevel D) : IClasses U ≃ Classes U :=
  Equiv.ofBijective forget
    ⟨integralCMForget_injective D C P.preservation P.composition P.unitCoherence
      P.associativity P.comparison P.symmetry P.stability P.square P.universality
      Z.obj.hom compatibility h s hs htor Z.property.torsionUnits Z.property.pairAdditivity,
      integralCMForget_surjective D C P fibreAmple htor Z compatibility h s hs⟩

@[simp] theorem integralCMClassEquiv_apply {U : HarrisLevel D} (q : IClasses U) :
    integralCMClassEquiv D C P fibreAmple htor Z compatibility h s hs U q = forget q := rfl

/-- The equivalence retains every arrow of the original Harris level category. -/
def integralCMClassTowerIso : itower ≅ tower :=
  NatIso.ofComponents
    (fun U => (integralCMClassEquiv D C P fibreAmple htor Z compatibility h s hs U).toIso)
    (by
      intro U V f
      ext q
      exact integralCMForget_classMap D C P.preservation P.composition P.unitCoherence
        P.associativity P.comparison P.symmetry P.stability P.square P.universality
        Z.obj.hom compatibility h s hs htor Z.property.torsionUnits
        Z.property.pairAdditivity f q)

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

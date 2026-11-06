import Langlands.Shimura.PEL.HarrisTaylorCMIsogenyModel
import Langlands.Shimura.PEL.HarrisTaylorCMIntegralClassImage
import Langlands.Shimura.PEL.HarrisIntegralLatticeIsogeny
import Langlands.Shimura.PEL.HarrisIntegralLatticeBounds
import Langlands.Shimura.PEL.HarrisIntegralOrderDescent
import Langlands.AbelianScheme.Tate.CommensurableInvariantLatticeRealizationStatement

/-! # Original CM representatives with normalized full integral Tate images -/

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
local notation "Data" => HarrisLevelData D C P.preservation P.composition P.unitCoherence
  P.associativity P.comparison P.symmetry P.stability P.square P.universality
  compatibility h s hs htor Z.property.torsionUnits
local notation "Rep" => IntegralCMRepresentative D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
  Z.obj.hom compatibility h s hs htor Z.property.torsionUnits
local notation "lev" U:max => (hodgeLevelFunctor D C).obj U
local notation "Normalized" => HarrisIntegralLevelCondition D C P compatibility h s hs htor
  Z.property.torsionUnits
local notation "lattice" => harrisIntegralLevelLattice D C P compatibility h s hs htor
  Z.property.torsionUnits
local notation "Rat" X:max =>
  letI := auxiliaryStarRing D C
  Tate.Rational (X).actionObj.abelianScheme (Over.mk s) (fun _ => True)
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
local notation "model" => cmPolarizedIsogenyModel D C P Z
local notation "modelIso" => cmPolarizedIsogenyModelIso D C P Z
local notation "modelQ" => cmPolarizedIsogenyModelMultiplier D C P Z
local notation "modelMult" => cmPolarizedIsogenyModel_multiple D C P Z

/-- An original determinant-and-dimension representative whose full integral
Tate image is normalized and whose order action is actual on that same scheme. -/
structure TateNormalizedCMRepresentative (U : HarrisLevel D) extends Rep U where
  normalized : letI := auxiliaryStarRing D C
    Normalized data.1 (lev U) data.2

local notation "NRep" => TateNormalizedCMRepresentative D C P Z compatibility h s hs htor

variable [IsAlgClosed Ω]
variable {U : HarrisLevel D}
variable (x : HarrisLevelData D C P.preservation P.composition P.unitCoherence
  P.associativity P.comparison P.symmetry P.stability P.square P.universality
  compatibility h s hs htor Z.property.torsionUnits U)
variable (hx : letI := auxiliaryStarRing D C
    D.HarrisTaylorCMDeterminantDimensionCondition C Z.obj.hom
      x.1.actionObj.abelianScheme x.1.actionObj.action)
variable (hU : ((hodgeLevelFunctor D C).obj U).toSubgroup ≤
  harrisIntegralAdeleStabilizer D C)

variable (B : AbelianScheme Z.obj.left)
variable (e : letI := auxiliaryStarRing D C
  Rationalization.of B ≅ Rationalization.of x.1.actionObj.abelianScheme)

variable (heq : letI := auxiliaryStarRing D C
  ∀ w : Tate.Rational x.1.actionObj.abelianScheme (Over.mk s) (fun _ => True),
    w ∈ harrisIntegralLevelLattice D C P compatibility h s hs htor
      Z.property.torsionUnits x.1 ((hodgeLevelFunctor D C).obj U) hU x.2 ↔
    ∃ b : GroupScheme.Tate.Full B.toGrp (Over.mk s),
      Tate.rationalHomMap (Over.mk s) (fun _ => True) e.hom
        (GroupScheme.Tate.toRational B.toGrp (Over.mk s) (fun _ => True) b) = w)

omit [IsCMField F] [IsScalarTower ℚ F A] [IsAlgClosed Ω] in
include hU heq in
/-- Exact realization of the original carried lattice normalizes the original
level transported along the unchanged rational isomorphism. -/
theorem cmIsogenyModel_level_normalized :
    letI := auxiliaryStarRing D C
    Normalized (model x.1 B e) (lev U)
      (transport x.1 (model x.1 B e) (lev U) (modelQ x.1 B e)
        (modelIso x.1 B e) (modelMult x.1 B e) x.2) := by
  let := auxiliaryStarRing D C
  apply (harrisIntegralLevelCondition_isogeny_iff D C P compatibility h s
    Z.property.pairAdditivity hs htor Z.property.torsionUnits
    x.1 (model x.1 B e) (lev U) hU (modelQ x.1 B e)
    (modelIso x.1 B e) (modelMult x.1 B e) x.2).mpr
  exact heq

/-- The same exact realized model, with its original transported level, actual
polarization, unchanged CM condition and recovered integral order action. -/
def cmTateNormalizedIsogenyRepresentative : NRep U := by
  letI := auxiliaryStarRing D C
  let y : Data U := ⟨model x.1 B e,
    transport x.1 (model x.1 B e) (lev U) (modelQ x.1 B e)
      (modelIso x.1 B e) (modelMult x.1 B e) x.2⟩
  have hn : Normalized y.1 (lev U) y.2 :=
    cmIsogenyModel_level_normalized D C P Z compatibility h s hs htor x hU B e heq
  exact {
    data := y
    condition := (cmPolarizedIsogenyModel_condition_iff D C P Z x.1 B e).mp hx
    restriction := harrisIntegralLevelActionRestriction D C P compatibility h s htor
      Z.property.torsionUnits hs y.1 (lev U) y.2 hn
    normalized := hn }

local notation "normalize" => cmTateNormalizedIsogenyRepresentative D C P Z
  compatibility h s hs htor x hx hU B e heq

/-- The normalized integral model lies in precisely the original CM class,
using the exact supplied inverse and its positive square multiplier. -/
theorem cmTateNormalizedIsogenyRepresentative_class :
    repClass (normalize).toIntegralCMRepresentative =
      mkClass x ((jointProof x.1).mp hx).1 ((jointProof x.1).mp hx).2 := by
  let := auxiliaryStarRing D C
  symm
  apply (HarrisNumericalWeilLevel.classOf_eq_iff D C hΦ P.preservation P.composition
    P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
    (D.harrisTaylorReflexStructure C Z.obj.hom) compatibility h s hs htor
    Z.property.torsionUnits Z.property.pairAdditivity L Z.obj.hom x (normalize).data
    ((jointProof x.1).mp hx).1
    ((jointProof (normalize).data.1).mp (normalize).condition).1
    ((jointProof x.1).mp hx).2
    ((jointProof (normalize).data.1).mp (normalize).condition).2).mpr
  exact ⟨modelQ x.1 B e, modelIso x.1 B e, modelMult x.1 B e, rfl⟩

section Existence

variable [CharZero Ω]
variable (realize : Tate.CommensurableInvariantLatticeRealizationStatement.{0})
variable (hfib : letI := auxiliaryStarRing D C
  ∀ (Q : Finset x.1.actionObj.abelianScheme.X.left) (t : Z.obj.left),
    (∀ z ∈ Q, x.1.actionObj.abelianScheme.X.hom z = t) →
      ∃ W : x.1.actionObj.abelianScheme.X.left.Opens,
        IsAffineOpen W ∧ ∀ z ∈ Q, z ∈ W)

include hU realize hfib in
/-- The generic lattice realization target, with its source fibre-affineness
hypothesis, supplies a normalized integral representative of the original class. -/
theorem exists_tateNormalizedCMRepresentative :
    ∃ y : NRep U, repClass y.toIntegralCMRepresentative =
      mkClass x ((jointProof x.1).mp hx).1 ((jointProof x.1).mp hx).2 := by
  let := auxiliaryStarRing D C
  obtain ⟨B, e, heq⟩ := realize htor h Z.obj.left Z.property.torsionUnits
    Ω s hs x.1.actionObj.abelianScheme hfib (lattice x.1 (lev U) hU x.2)
    (harrisIntegralLevelLattice_monodromy D C P compatibility h s hs htor
      Z.property.torsionUnits x.1 (lev U) hU x.2)
    (harrisIntegralLevelLattice_integerBounds D C P compatibility h s hs htor
      Z.property.torsionUnits x.1 (lev U) hU x.2)
  exact ⟨cmTateNormalizedIsogenyRepresentative D C P Z compatibility h s hs htor
      x hx hU B e heq,
    cmTateNormalizedIsogenyRepresentative_class D C P Z compatibility h s hs htor
      x hx hU B e heq⟩

end Existence

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

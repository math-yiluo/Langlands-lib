import Langlands.Shimura.PEL.HarrisTaylorCMDivisionQuasiProjectiveDecomposition
import Langlands.Shimura.PEL.HarrisTaylorCMOrdinaryPresheaf
import Langlands.Shimura.PEL.HarrisIntegralSourceLevels
import Langlands.Shimura.ProPLevels
import Langlands.AlgebraicGeometry.Picard.ProperFibreAmpleAffineOpenProof
import Langlands.AbelianScheme.Tate.CommensurableInvariantLatticeRealizationProof

/-! # Normal sublevels and ordinary quasi-projective CM representers -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
open Langlands.AbelianScheme.PolarizedFiniteLevel (Prerequisites)
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.FiniteEtale Langlands.GroupScheme
open Langlands.AlgebraicGeometry

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

local notation "HodgeGroup" => ScalarExtensionSimilitudePoints A A
  (Global.FiniteAdeles ℚ) (D.harrisHodgePELForm C)
local notation "lev" U:max => (hodgeLevelFunctor D C).obj U

omit [IsCMField F] [IsScalarTower ℚ F A] in
/-- Every original small level has a small normal sublevel whose Hodge transport
lies inside a prescribed open subgroup of the actual scalar-extension group. -/
theorem exists_smallCMNormalSublevel_le_hodgeOpenSubgroup
    (U : SmallCMLevel D) (K : OpenSubgroup HodgeGroup) :
    ∃ V : SmallCMLevel D, V.obj.subgroup ≤ U.obj.subgroup ∧
      (V.obj.subgroup.subgroupOf U.obj.subgroup).Normal ∧
      (lev V.obj).toSubgroup ≤ K.toSubgroup := by
  let := D.finite
  let : Module.Finite ℚ A := Module.Finite.trans F A
  let e := D.harrisFiniteAdelicScalarExtensionContinuousEquiv
    (D.harrisHodgePELUnit C) (D.harrisHodgePELUnit_skew C)
  let H := K.comap e.toMonoidHom e.continuous
  let W := U.obj.normalCoreIn H.toSubgroup H.isOpen
  have hWU : W.subgroup ≤ U.obj.subgroup := U.obj.normalCoreIn_le_self H.isOpen
  refine ⟨⟨W, U.property.mono hWU⟩, hWU,
    CompactOpenLevel.normalCoreIn_normal U.obj H.isOpen, ?_⟩
  intro g hg
  obtain ⟨x, rfl⟩ := e.surjective g
  have hx : x ∈ W.subgroup := (hodgeLevelFunctor_obj_mem D C W x).mp hg
  exact U.obj.normalCoreIn_le H.isOpen hx

variable (P : Prerequisites.{0})
  (dualityNaturality : DualAbelianBaseChangeNaturalityStatement.{0})
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  (htor : TorsionFiniteEtaleStatement.{0})

local notation "tests" => admissibleTestPoints D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality

/-- A quasi-projective scheme representing the ordinary actual-isomorphism
classes of normalized CM data at a source-stabilizing small level. -/
structure CMOrdinaryQuasiProjectiveRepresentation (U : SmallCMLevel D)
    (hU : (lev U.obj).toSubgroup ≤ harrisIntegralAdeleStabilizer D C) where
  scheme : Over (Spec (.of F))
  dim : ℕ
  embedding : scheme.left ⟶ ProjectiveSpace F dim
  isImmersion : IsImmersion embedding
  embedding_comp : embedding ≫ projectiveSpaceToSpec F dim = scheme.hom
  represents : tests scheme ≅
    tateNormalizedCMOrdinaryDisconnectedPresheaf D C P dualityNaturality
      P.polarizationBaseChange compatibility h htor U.obj hU

local notation "OrdinaryQP" => CMOrdinaryQuasiProjectiveRepresentation D C P
  dualityNaturality compatibility h htor
local notation "CMQP" => CMLevelQuasiProjectiveRepresentation D C P.preservation
  P.composition P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square
  P.universality dualityNaturality P.polarizationBaseChange compatibility h htor

/-- The same scheme represents the original rational-isogeny presheaf, using
its published comparison with ordinary normalized models. -/
def CMOrdinaryQuasiProjectiveRepresentation.toQuasiProjective
    {U : SmallCMLevel D}
    {hU : (lev U.obj).toSubgroup ≤ harrisIntegralAdeleStabilizer D C}
    (R : OrdinaryQP U hU) : CMQP U where
  scheme := R.scheme
  dim := R.dim
  embedding := R.embedding
  isImmersion := R.isImmersion
  embedding_comp := R.embedding_comp
  represents := R.represents ≪≫
    tateNormalizedCMOrdinaryDisconnectedIso D C P dualityNaturality P.polarizationBaseChange
      compatibility h htor properFibreAmpleAffineOpen Tate.commensurableInvariantLatticeRealization
      U.obj hU

/-- It suffices to represent the ordinary normalized problem for all small
levels whose Hodge transports are inside a single prescribed open subgroup
and the source-lattice stabilizer. Their relative normal refinements give the
sublevels of the published division-case premise. -/
theorem divisionCMNormalSublevelRepresentabilityStatement_of_ordinary
    (K : OpenSubgroup HodgeGroup)
    (hrep : D.IsDivision → ∀ (U : SmallCMLevel D)
      (_ : (lev U.obj).toSubgroup ≤ K.toSubgroup)
      (hU : (lev U.obj).toSubgroup ≤ harrisIntegralAdeleStabilizer D C),
      Nonempty (OrdinaryQP U hU)) :
    DivisionCMNormalSublevelRepresentabilityStatement D C P.preservation P.composition
      P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
      dualityNaturality P.polarizationBaseChange compatibility h htor := by
  intro hD U
  obtain ⟨V, hVU, hnormal, hV⟩ := exists_smallCMNormalSublevel_le_hodgeOpenSubgroup D C U
    (K ⊓ harrisIntegralAdeleOpenStabilizer D C)
  obtain ⟨R⟩ := hrep hD V (fun _ hx => (hV hx).1) (fun _ hx => (hV hx).2)
  exact ⟨V, hVU, hnormal, ⟨R.toQuasiProjective D C P dualityNaturality compatibility h htor⟩⟩

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

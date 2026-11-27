import Langlands.Shimura.PEL.HarrisTaylorCMNormalQuotientPremiseStatements
import Langlands.Shimura.PEL.HarrisTaylorCMClassTransitivity
import Langlands.Shimura.PEL.HarrisTaylorCMBaseAdmissibility
import Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeExistenceProof
import Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeGeometryProof

/-! # Fibres of the CM forgetting transition on connected tests -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
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
  (preservation : pullbackTensorComparisonIsIsoStatement.{0})
  (composition : PullbackTensorCompositionStatement.{0})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{0})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{0})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{0})
  (symmetry : PullbackTensorSymmetryStatement.{0})
  (stability : PicardZeroPullbackStatement.{0})
  (square : MumfordBundlePicardZeroStatement.{0})
  (universality : PicardZeroUniversalBaseChangeStatement.{0})
  (dualityNaturality : DualAbelianBaseChangeNaturalityStatement.{0})
  (polarizationStability : PolarizationBaseChangeStatement.{0})
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  (htor : TorsionFiniteEtaleStatement.{0})

set_option maxHeartbeats 2000000 in
/-- On a connected admissible test, two fine classes with the same coarse class
differ by inverse right translation by an element of the coarse level. -/
theorem cmNormalSublevelConnectedFibre :
    CMNormalSublevelConnectedFibreStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor := by
  intro U' U hle _ T hconn c₁ c₂ hc
  have hp : AdmissibleCMBase D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality T.obj :=
    (admissibleCMBase_iff_dualGeometry D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality T.obj).mpr
      (fun B => ⟨relativeDualSchemeExistence _ B,
        relativeDualSchemeGeometry _ B (relativeDualSchemeExistence _ B)⟩)
  let X : AdmissibleCMBaseCategory D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality := ⟨T.obj, hp⟩
  have : Nonempty T.obj.left := inferInstance
  let a := HarrisGeometricPoint.ofResidue T.obj.left (Classical.arbitrary T.obj.left)
  let c : _root_.ConnectedComponents T.obj.left := .mk (Classical.arbitrary _)
  let e := disconnectedClassTowerConnectedIso D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor T hp c ≪≫
    unpointedClassTowerEvaluationIso D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality compatibility h htor X a
  let : ∀ k : GroupScheme.Tate.Index (fun _ => True),
      IsFinite (mu T.obj.left k.val).X.hom := hp.muFinite
  let : ∀ k : GroupScheme.Tate.Index (fun _ => True),
      Etale (mu T.obj.left k.val).X.hom := hp.muEtale
  let : QuasiSeparatedSpace T.obj.left := hp.quasiSeparated
  have hx : (geometricClassTower D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality T.obj.hom compatibility h htor
        hp.torsionUnits hp.pairAdditivity a).map (CompactOpenLevel.inclusion hle)
        (e.hom.app U'.obj c₁) =
      (geometricClassTower D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality T.obj.hom compatibility h htor
        hp.torsionUnits hp.pairAdditivity a).map (CompactOpenLevel.inclusion hle)
        (e.hom.app U'.obj c₂) :=
    (NatTrans.naturality_apply e.hom (CompactOpenLevel.inclusion hle) c₁).symm.trans
      ((congrArg (e.hom.app U.obj) hc).trans
        (NatTrans.naturality_apply e.hom (CompactOpenLevel.inclusion hle) c₂))
  obtain ⟨g, hg⟩ := classMap_exists_normalTranslate D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    T.obj.hom compatibility h a.hom a.finiteFibers htor hp.torsionUnits hp.pairAdditivity
    U.obj U'.obj hle _ _ hx
  refine ⟨g, (e.app U'.obj).toEquiv.injective ?_⟩
  change e.hom.app U'.obj ((disconnectedClassTower D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      compatibility h htor T).map (CompactOpenLevel.normalInverseArrow U.obj U'.obj hle g) c₁) =
    e.hom.app U'.obj c₂
  exact (NatTrans.naturality_apply e.hom
    (CompactOpenLevel.normalInverseArrow U.obj U'.obj hle g) c₁).trans hg

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

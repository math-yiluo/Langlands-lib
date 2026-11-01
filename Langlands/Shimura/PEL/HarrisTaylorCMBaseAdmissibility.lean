import Langlands.Shimura.PEL.HarrisTaylorCMPolarizedDisconnectedPresheaf
import Langlands.AbelianScheme.LieBaseChangeNaturalityProof
import Langlands.GroupScheme.MuFiniteEtaleProof
import Langlands.AlgebraicGeometry.Picard.LineBundleDualEvaluation
import Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeExistenceStatement
import Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeMapAdditivityProof
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Reduction of CM base admissibility to actual dual geometry -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry Langlands.GroupScheme
open GroupScheme.Tate (Index)

/-- The dual-scheme existence and geometry needed on a specified base.
This predicate retains the actual universal Picard-zero parameter. -/
def CMBaseDualGeometry (S : Scheme.{0}) : Prop :=
  ∀ B : AbelianScheme S, ∃ hB : HasDualScheme B, DualSchemeGeometry B hB

/-- The evaluation and additivity fields are derived from the same actual dual. -/
def dualEvaluationDataOfGeometry
    (preservation : pullbackTensorComparisonIsIsoStatement.{0})
    (stability : PicardZeroPullbackStatement.{0})
    {S : Scheme.{0}} [QuasiSeparatedSpace S]
    (B : AbelianScheme S) (hB : HasDualScheme B) (geometry : DualSchemeGeometry B hB) :
    DualEvaluationData preservation stability B := by
  let P : LineBundle ((relativeSpace B.X.hom).obj (dualScheme B hB)) :=
    ⟨(poincareFamily B hB).obj.carrier, (poincareFamily B hB).property⟩
  let inverseExists := P.exists_tensorObj_iso_structureSheaf
  exact
    { hasDual := hB
      geometry := geometry
      inversePoincare := Classical.choose inverseExists
      evaluation := Classical.choice (Classical.choose_spec inverseExists)
      dualEndAdditivity := relativeDualSchemeMapAdditivity preservation stability S B B hB hB }

/-- Nonempty constrained dual data is equivalent to actual dual existence
with geometry; inverse Poincare bundles and additivity add no further premise. -/
theorem nonempty_dualEvaluationData_iff
    (preservation : pullbackTensorComparisonIsIsoStatement.{0})
    (stability : PicardZeroPullbackStatement.{0})
    {S : Scheme.{0}} [QuasiSeparatedSpace S] (B : AbelianScheme S) :
    Nonempty (DualEvaluationData preservation stability B) ↔
      ∃ hB : HasDualScheme B, DualSchemeGeometry B hB := by
  constructor
  · rintro ⟨W⟩
    exact ⟨W.hasDual, W.geometry⟩
  · rintro ⟨hB, geometry⟩
    exact ⟨dualEvaluationDataOfGeometry preservation stability B hB geometry⟩

/-- A positive torsion index is invertible on every actual characteristic-zero
field scheme, by the structural map on sections. -/
theorem cmBaseTorsionUnit {K : Type} [Field K] [CharZero K]
    {S : Scheme.{0}} (p : S ⟶ Spec (.of K)) (k : Index (fun _ => True)) :
    IsUnit (k.val : Γ(S, ⊤)) := by
  have hu : IsUnit (k.val : K) :=
    isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.ne_of_gt k.property.1))
  simpa only [map_natCast] using
    hu.map ((Scheme.ΓSpecIso (.of K)).inv ≫ p.appTop).hom

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

local notation "admissible" => AdmissibleCMBase D C preservation composition
  unitCoherence associativity comparison symmetry stability square universality
local notation "componentwise" => ComponentwiseAdmissibleCMBase D C preservation
  composition unitCoherence associativity comparison symmetry stability square universality

omit [IsCMField F] [IsScalarTower ℚ F A]
/-- The ordered-pair additivity used in the normalized quotient follows from
published additivity of actual dual maps. -/
theorem positivePairAdditivity {S : Scheme.{0}} [QuasiSeparatedSpace S] :
    PositivePairAdditivity D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality (S := S) := by
  let := auxiliaryStarRing D C
  intro X Y
  exact relativeDualSchemeMapAdditivity preservation stability S
    X.actionObj.abelianScheme Y.actionObj.abelianScheme X.hasDual Y.hasDual

/-- On an actual connected locally Noetherian CM base, all admissibility
fields except dual existence and geometry follow from published results. -/
theorem admissibleCMBase_iff_dualGeometry
    (X : Over (Spec (.of F))) [ConnectedSpace X.left] [IsLocallyNoetherian X.left] :
    admissible X ↔ CMBaseDualGeometry X.left := by
  constructor
  · intro hX B
    exact (nonempty_dualEvaluationData_iff preservation stability B).mp (hX.dualExists B)
  · intro hd
    refine
      { connected := inferInstance
        locallyNoetherian := inferInstance
        quasiSeparated := inferInstance
        torsionUnits := cmBaseTorsionUnit X.hom
        muFinite := ?_
        muEtale := ?_
        lieNaturality := (lieBaseChangeNaturalityStatements X.left).1
        pairAdditivity := positivePairAdditivity D C preservation composition unitCoherence
          associativity comparison symmetry stability square universality
        dualExists := ?_ }
    · intro k
      exact (muFiniteEtale X.left k.val k.property.1 (cmBaseTorsionUnit X.hom k)).1
    · intro k
      exact (muFiniteEtale X.left k.val k.property.1 (cmBaseTorsionUnit X.hom k)).2
    · intro B
      exact (nonempty_dualEvaluationData_iff preservation stability B).mpr (hd B)

/-- The same exact reduction on every actual connected open component. -/
theorem componentwiseAdmissibleCMBase_iff_dualGeometry
    (X : Over (Spec (.of F))) [IsLocallyNoetherian X.left] :
    componentwise X ↔
      ∀ c : _root_.ConnectedComponents X.left, CMBaseDualGeometry (componentScheme X.left c) := by
  constructor
  · intro hX c
    let : ConnectedSpace (componentCMOver X c).left := componentSchemeConnected X.left c
    let : IsLocallyNoetherian (componentCMOver X c).left :=
      componentSchemeLocallyNoetherian X.left c
    exact (admissibleCMBase_iff_dualGeometry D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality (componentCMOver X c)).mp
        (hX.components c)
  · intro hd
    refine ⟨inferInstance, fun c => ?_⟩
    let : ConnectedSpace (componentCMOver X c).left := componentSchemeConnected X.left c
    let : IsLocallyNoetherian (componentCMOver X c).left :=
      componentSchemeLocallyNoetherian X.left c
    exact (admissibleCMBase_iff_dualGeometry D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality (componentCMOver X c)).mpr
        (hd c)

/-- The two separately stated relative dual assertions supply the remaining
obligation. This is a conditional bridge, not a proof of either assertion. -/
theorem componentwiseAdmissibleCMBase_of_relativeDual
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (X : Over (Spec (.of F))) [IsLocallyNoetherian X.left] :
    componentwise X := by
  apply (componentwiseAdmissibleCMBase_iff_dualGeometry D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality X).mpr
  intro c B
  exact ⟨existence _ B, geometry _ B (existence _ B)⟩

/-- A smooth CM scheme is locally Noetherian. Its admissibility therefore
has only the same two relative dual assertions left as premises. -/
theorem smoothComponentwiseAdmissibleCMBase_of_relativeDual
    (existence : RelativeDualSchemeExistenceStatement.{0})
    (geometry : RelativeDualSchemeGeometryStatement.{0})
    (X : Over (Spec (.of F))) [Smooth X.hom] :
    componentwise X := by
  let : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  exact componentwiseAdmissibleCMBase_of_relativeDual D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    existence geometry X

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

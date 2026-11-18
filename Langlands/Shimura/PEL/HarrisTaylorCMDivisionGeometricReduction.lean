import Langlands.Shimura.PEL.HarrisTaylorCMDivisionAssembly
import Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeExistenceProof
import Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeGeometryProof

/-! # Unconditional geometric reduction of the division-case CM target -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme HarrisPolarizedWeilLevel
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

/-- Geometric representation data at a small level is an exact
representation, with the relative dual premises discharged by the Library
theorems `relativeDualSchemeExistence` and `relativeDualSchemeGeometry`. -/
def CMLevelGeometricRepresentation.toRepresentation'
    {U : SmallCMLevel D}
    (R : CMLevelGeometricRepresentation D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor U) :
    CMLevelRepresentation D C preservation composition unitCoherence associativity
      comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor U :=
  R.toRepresentation D C preservation composition unitCoherence associativity comparison
    symmetry stability square universality dualityNaturality polarizationStability
    compatibility h htor relativeDualSchemeExistence.{0} relativeDualSchemeGeometry.{0}

/-- At a fixed small level, the exact pointwise representability statement is
equivalent to the existence of geometric representation data. -/
theorem cmLevelRepresentabilityStatement_iff_geometric'
    (U : SmallCMLevel D) :
    CMLevelRepresentabilityStatement D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor U ↔
      Nonempty (CMLevelGeometricRepresentation D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor U) :=
  cmLevelRepresentabilityStatement_iff_geometric D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor
    relativeDualSchemeExistence.{0} relativeDualSchemeGeometry.{0} U

/-- The exact consequent `CMRepresentabilityStatement` of the division target
is equivalent to geometric representability at every small level. -/
theorem cmRepresentabilityStatement_iff_geometric' :
    CMRepresentabilityStatement D C preservation composition unitCoherence associativity
        comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor ↔
      CMGeometricRepresentabilityStatement D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor :=
  cmRepresentabilityStatement_iff_geometric D C preservation composition unitCoherence
    associativity comparison symmetry stability square universality dualityNaturality
    polarizationStability compatibility h htor
    relativeDualSchemeExistence.{0} relativeDualSchemeGeometry.{0}

/-- The division-case target is equivalent to division-case geometric
representability. This is a reformulation, not a proof of either side. -/
theorem divisionCMRepresentabilityStatement_iff_geometric :
    DivisionCMRepresentabilityStatement D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor ↔
      (D.IsDivision →
        CMGeometricRepresentabilityStatement D C preservation composition unitCoherence
          associativity comparison symmetry stability square universality dualityNaturality
          polarizationStability compatibility h htor) :=
  imp_congr_right fun _ => cmRepresentabilityStatement_iff_geometric' D C preservation
    composition unitCoherence associativity comparison symmetry stability square
    universality dualityNaturality polarizationStability compatibility h htor

/-- The division-case target follows from division-case geometric
representability alone; the relative dual premises of
`divisionCMRepresentabilityStatement_of_geometric` are discharged by Library
theorems. The remaining premise is unproved. -/
theorem divisionCMRepresentabilityStatement_of_geometric'
    (hgeom : D.IsDivision →
      CMGeometricRepresentabilityStatement D C preservation composition unitCoherence
        associativity comparison symmetry stability square universality dualityNaturality
        polarizationStability compatibility h htor) :
    DivisionCMRepresentabilityStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor :=
  divisionCMRepresentabilityStatement_of_geometric D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor
    relativeDualSchemeExistence.{0} relativeDualSchemeGeometry.{0} hgeom

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

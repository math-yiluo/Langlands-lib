import Langlands.Shimura.PEL.HarrisTaylorCMDivisionPremiseStatements

/-! # Division-case quasi-projective representability through normal sublevels -/

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

/-- Descent of quasi-projective representability along normal sublevels: for
small levels `U' ≤ U` with `U'` normal in `U`, quasi-projective
representation data at `U'` give quasi-projective representation data at `U`.
There is no division hypothesis. -/
def CMQuasiProjectiveNormalQuotientStatement : Prop :=
  ∀ U' U : SmallCMLevel D, U'.obj.subgroup ≤ U.obj.subgroup →
    (U'.obj.subgroup.subgroupOf U.obj.subgroup).Normal →
    Nonempty (CMLevelQuasiProjectiveRepresentation D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor U') →
    Nonempty (CMLevelQuasiProjectiveRepresentation D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor U)

/-- Division-case quasi-projective representability at some normal sublevel:
if the algebra is a division algebra, then every small level `U` contains a
small level `U'`, normal in `U`, with quasi-projective representation data. -/
def DivisionCMNormalSublevelRepresentabilityStatement : Prop :=
  D.IsDivision → ∀ U : SmallCMLevel D, ∃ U' : SmallCMLevel D,
    U'.obj.subgroup ≤ U.obj.subgroup ∧
      (U'.obj.subgroup.subgroupOf U.obj.subgroup).Normal ∧
      Nonempty (CMLevelQuasiProjectiveRepresentation D C preservation composition
        unitCoherence associativity comparison symmetry stability square universality
        dualityNaturality polarizationStability compatibility h htor U')

/-- Normal-quotient descent and normal-sublevel representability give the
division-case quasi-projective premise. -/
theorem divisionCMQuasiProjectiveRepresentabilityStatement_of_normalSublevel
    (hq : CMQuasiProjectiveNormalQuotientStatement D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor)
    (hs : DivisionCMNormalSublevelRepresentabilityStatement D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor) :
    DivisionCMQuasiProjectiveRepresentabilityStatement D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor := by
  intro hD U
  obtain ⟨U', hle, hnormal, hrep⟩ := hs hD U
  exact hq U' U hle hnormal hrep

/-- The division-case quasi-projective premise gives normal-sublevel
representability, with `U' = U`. -/
theorem divisionCMNormalSublevelRepresentabilityStatement_of_quasiProjective
    (hrep : DivisionCMQuasiProjectiveRepresentabilityStatement D C preservation
      composition unitCoherence associativity comparison symmetry stability square
      universality dualityNaturality polarizationStability compatibility h htor) :
    DivisionCMNormalSublevelRepresentabilityStatement D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor := by
  intro hD U
  refine ⟨U, le_rfl, ?_, hrep hD U⟩
  rw [Subgroup.subgroupOf_self]
  infer_instance

/-- Under normal-quotient descent, the division-case quasi-projective premise is
equivalent to normal-sublevel representability. -/
theorem divisionCMQuasiProjectiveRepresentabilityStatement_iff_normalSublevel
    (hq : CMQuasiProjectiveNormalQuotientStatement D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor) :
    DivisionCMQuasiProjectiveRepresentabilityStatement D C preservation composition
        unitCoherence associativity comparison symmetry stability square universality
        dualityNaturality polarizationStability compatibility h htor ↔
      DivisionCMNormalSublevelRepresentabilityStatement D C preservation composition
        unitCoherence associativity comparison symmetry stability square universality
        dualityNaturality polarizationStability compatibility h htor :=
  ⟨divisionCMNormalSublevelRepresentabilityStatement_of_quasiProjective D C
      preservation composition unitCoherence associativity comparison symmetry stability
      square universality dualityNaturality polarizationStability compatibility h htor,
    divisionCMQuasiProjectiveRepresentabilityStatement_of_normalSublevel D C
      preservation composition unitCoherence associativity comparison symmetry stability
      square universality dualityNaturality polarizationStability compatibility h htor hq⟩

/-- The division-case target follows from normal-quotient descent,
normal-sublevel representability, and the lifting and valuative premises. -/
theorem divisionCMRepresentabilityStatement_of_normalSublevel
    (hq : CMQuasiProjectiveNormalQuotientStatement D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor)
    (hs : DivisionCMNormalSublevelRepresentabilityStatement D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor)
    (hlift : DivisionCMArtinianLiftingStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor)
    (hval : DivisionCMDiscreteValuativeExistenceStatement D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor) :
    DivisionCMRepresentabilityStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor :=
  divisionCMRepresentabilityStatement_of_premiseStatements D C preservation composition
    unitCoherence associativity comparison symmetry stability square universality
    dualityNaturality polarizationStability compatibility h htor
    (divisionCMQuasiProjectiveRepresentabilityStatement_of_normalSublevel D C
      preservation composition unitCoherence associativity comparison symmetry stability
      square universality dualityNaturality polarizationStability compatibility h htor
      hq hs)
    hlift hval

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

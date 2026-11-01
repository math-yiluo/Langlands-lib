import Langlands.Shimura.PEL.HarrisIntegralRosatiEquations
import Langlands.AlgebraicGeometry.Picard.DualAbelianBaseChangeNaturalityProof

/-! # Actual base change of finite integral Harris Rosati equations -/

noncomputable section

open CategoryTheory AlgebraicGeometry Module
open scoped BigOperators

universe s

namespace Langlands.Shimura.PEL.HarrisPolarizedWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

variable {E F A : Type}
    [Field E] [NumberField E] [IsTotallyReal E]
    [Field F] [NumberField F] [IsTotallyComplex F]
    [Algebra E F] [IsQuadraticExtension E F]
    [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
    [Algebra ℚ A] [IsScalarTower ℚ E A]
    {n : ℕ} {Φ : (E →+* ℝ) → (F →+* ℂ)}
    (D : CentralSimpleUnitaryData E F A n)
    (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)

variable
    (preservation : pullbackTensorComparisonIsIsoStatement.{s})
    (composition : PullbackTensorCompositionStatement.{s})
    (unitCoherence : PullbackTensorUnitCoherenceStatement.{s})
    (associativity : ExplicitPullbackTensorAssociativityStatement.{s})
    (comparison : TensorMonoidalLeftUnitorComparisonStatement.{s})
    (symmetry : PullbackTensorSymmetryStatement.{s})
    (stability : PicardZeroPullbackStatement.{s})
    (universality : PicardZeroUniversalBaseChangeStatement.{s})
    (compatibility : DualAbelianBaseChangeStatement.{s})
    {S S' : Scheme.{s}} (b : S' ⟶ S) (B : Langlands.AbelianScheme S)
    (hB : HasDualScheme B)
    (MB : LineBundle ((relativeSpace B.X.hom).obj (dualScheme B hB)))
    (evaluationB : tensorObj (poincareFamily B hB).obj.carrier MB.obj ≅
      structureSheaf ((relativeSpace B.X.hom).obj (dualScheme B hB)))
    (geometryB : DualSchemeGeometry B hB)
    (hB' : HasDualScheme ((baseChange b).obj B))
    (MB' : LineBundle ((relativeSpace ((baseChange b).obj B).X.hom).obj
      (dualScheme ((baseChange b).obj B) hB')))
    (evaluationB' : tensorObj (poincareFamily ((baseChange b).obj B) hB').obj.carrier MB'.obj ≅
      structureSheaf ((relativeSpace ((baseChange b).obj B).X.hom).obj
        (dualScheme ((baseChange b).obj B) hB')))
    (geometryB' : DualSchemeGeometry ((baseChange b).obj B) hB')

local notation "DB" => dualAbelianSchemeFromEvaluation B hB geometryB preservation MB
  evaluationB stability composition unitCoherence associativity comparison symmetry
local notation "dualInt" => dualAbelianSchemeMapFromEvaluation hB geometryB preservation MB
  evaluationB stability composition unitCoherence associativity comparison symmetry
  hB geometryB MB evaluationB
local notation "dualInt'" => dualAbelianSchemeMapFromEvaluation hB' geometryB' preservation MB'
  evaluationB' stability composition unitCoherence associativity comparison symmetry
  hB' geometryB' MB' evaluationB'
local notation "beta" => dualAbelianBaseChangeIso preservation stability composition
  unitCoherence associativity comparison symmetry universality compatibility b B
  hB geometryB MB evaluationB hB' geometryB' MB' evaluationB'
local notation "pullLam" => dualAbelianBaseChangeMap preservation stability composition
  unitCoherence associativity comparison symmetry universality compatibility b B
  hB geometryB MB evaluationB hB' geometryB' MB' evaluationB'
local notation "O" => D.harrisHodgePELIntegralOrder C
local notation "basisO" => D.harrisHodgePELIntegralBasis C

private theorem integralRosatiEquation_baseChange
    {f g : CategoryTheory.End B} {lam : B ⟶ DB}
    (h : f ≫ lam = lam ≫ dualInt g) :
    (baseChange b).map f ≫ pullLam lam =
      pullLam lam ≫ dualInt' ((baseChange b).map g) := by
  change (baseChange b).map f ≫ ((baseChange b).map lam ≫ (beta).hom) =
    ((baseChange b).map lam ≫ (beta).hom) ≫ dualInt' ((baseChange b).map g)
  rw [← Category.assoc, ← Functor.map_comp, h, Functor.map_comp, Category.assoc]
  rw [dualAbelianBaseChangeNaturality preservation stability composition unitCoherence
    associativity comparison symmetry universality compatibility S S' b B B
    hB geometryB MB evaluationB hB geometryB MB evaluationB
    hB' geometryB' MB' evaluationB' hB' geometryB' MB' evaluationB']
  exact (Category.assoc _ _ _).symm

/-- Every actual order Rosati equation is preserved by arbitrary base change. -/
theorem IntegralRosatiEquations.baseChange
    {a : O →+* CategoryTheory.End B} {lam : B ⟶ DB}
    (h : IntegralRosatiEquations D C preservation composition unitCoherence associativity
      comparison symmetry stability B hB MB evaluationB geometryB a lam) :
    IntegralRosatiEquations D C preservation composition unitCoherence associativity
      comparison symmetry stability ((baseChange b).obj B) hB' MB' evaluationB' geometryB'
      (baseChangeOrderAction b B a) (pullLam lam) := by
  intro x
  exact integralRosatiEquation_baseChange preservation composition unitCoherence associativity
    comparison symmetry stability universality compatibility b B
    hB MB evaluationB geometryB hB' MB' evaluationB' geometryB' (h x)

/-- The actual finite basis equations are preserved without dual-additivity assumptions. -/
theorem IntegralRosatiBasisEquations.baseChange
    {a : O →+* CategoryTheory.End B} {lam : B ⟶ DB}
    (h : IntegralRosatiBasisEquations D C preservation composition unitCoherence associativity
      comparison symmetry stability B hB MB evaluationB geometryB a lam) :
    IntegralRosatiBasisEquations D C preservation composition unitCoherence associativity
      comparison symmetry stability ((baseChange b).obj B) hB' MB' evaluationB' geometryB'
      (baseChangeOrderAction b B a) (pullLam lam) := by
  intro k
  exact integralRosatiEquation_baseChange preservation composition unitCoherence associativity
    comparison symmetry stability universality compatibility b B
    hB MB evaluationB geometryB hB' MB' evaluationB' geometryB' (h k)

/-- Pullback of each endomorphism preserves the explicit finite Rosati equations. -/
theorem IntegralRosatiTupleEquations.baseChange
    {r : IntegralActionSolutions basisO B} {lam : B ⟶ DB}
    (h : IntegralRosatiTupleEquations D C preservation composition unitCoherence associativity
      comparison symmetry stability B hB MB evaluationB geometryB r lam) :
    IntegralRosatiTupleEquations D C preservation composition unitCoherence associativity
      comparison symmetry stability ((baseChange b).obj B) hB' MB' evaluationB' geometryB'
      (integralActionSolutionsBaseChange basisO b B r) (pullLam lam) := by
  intro k
  have hk := integralRosatiEquation_baseChange preservation composition unitCoherence
    associativity comparison symmetry stability universality compatibility b B
    hB MB evaluationB geometryB hB' MB' evaluationB' geometryB' (h k)
  change (baseChangeEnd b B) (r.val k) ≫ pullLam lam =
    pullLam lam ≫ dualInt' ((baseChangeEnd b B)
      (∑ j, (basisO).repr (D.harrisHodgePELIntegralInvolution C (basisO k)) j • r.val j))
    at hk
  simpa only [map_sum, map_zsmul, baseChangeEnd_apply,
    integralActionSolutionsBaseChange_apply] using hk

/-- Transport the actual finite action tuples satisfying Rosati for a fixed map. -/
def integralRosatiSolutionsBaseChange (lam : B ⟶ DB) :
    {r : IntegralActionSolutions basisO B //
      IntegralRosatiTupleEquations D C preservation composition unitCoherence associativity
        comparison symmetry stability B hB MB evaluationB geometryB r lam} →
    {r : IntegralActionSolutions basisO ((baseChange b).obj B) //
      IntegralRosatiTupleEquations D C preservation composition unitCoherence associativity
        comparison symmetry stability ((baseChange b).obj B) hB' MB' evaluationB' geometryB'
        r (pullLam lam)} :=
  fun r => ⟨integralActionSolutionsBaseChange basisO b B r.val,
    r.property.baseChange D C preservation composition unitCoherence associativity
      comparison symmetry stability universality compatibility b B
      hB MB evaluationB geometryB hB' MB' evaluationB' geometryB'⟩

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel

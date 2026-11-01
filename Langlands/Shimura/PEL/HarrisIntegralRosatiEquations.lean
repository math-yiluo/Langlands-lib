import Langlands.Shimura.PEL.HarrisIntegralRosatiCompatibility
import Mathlib.CategoryTheory.Linear.Basic

/-! # Finite equations for all actual integral Rosati identities -/

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
    {S : Scheme.{s}} (B : Langlands.AbelianScheme S)
    (hB : HasDualScheme B)
    (additivity : DualSchemeMapAdditivity preservation stability B B hB hB)
    (MB : LineBundle ((relativeSpace B.X.hom).obj (dualScheme B hB)))
    (evaluationB : tensorObj (poincareFamily B hB).obj.carrier MB.obj ≅
      structureSheaf ((relativeSpace B.X.hom).obj (dualScheme B hB)))
    (geometryB : DualSchemeGeometry B hB)

local notation "DB" => dualAbelianSchemeFromEvaluation B hB geometryB preservation MB
  evaluationB stability composition unitCoherence associativity comparison symmetry
local notation "dualInt" => dualAbelianSchemeMapFromEvaluation hB geometryB preservation MB
  evaluationB stability composition unitCoherence associativity comparison symmetry
  hB geometryB MB evaluationB
local notation "dualAdd" => dualAbelianSchemeMapAddHom preservation composition unitCoherence
  associativity comparison symmetry stability hB hB additivity MB evaluationB MB evaluationB
  geometryB geometryB
local notation "O" => D.harrisHodgePELIntegralOrder C
local notation "basisO" => D.harrisHodgePELIntegralBasis C
local notation "tauO" => D.harrisHodgePELIntegralInvolution C
local notation "BasisEquations" => IntegralRosatiBasisEquations D C preservation composition
  unitCoherence associativity comparison symmetry stability B hB MB evaluationB geometryB

/-- Rosati equations on the entire actual integral order. -/
def IntegralRosatiEquations (a : O →+* CategoryTheory.End B) (lam : B ⟶ DB) : Prop :=
  ∀ x, a x ≫ lam = lam ≫ dualInt (a (tauO x))

include additivity in
/-- Actual integral Rosati compatibility is detected on the finite integer basis. -/
theorem integralRosatiEquations_iff_basis
    (a : O →+* CategoryTheory.End B) (lam : B ⟶ DB) :
    IntegralRosatiEquations D C preservation composition unitCoherence associativity
      comparison symmetry stability B hB MB evaluationB geometryB a lam ↔
      BasisEquations a lam := by
  constructor
  · intro h k
    exact h (basisO k)
  · intro h
    let L : O →ₗ[ℤ] (B ⟶ DB) :=
      (Linear.rightComp ℤ B lam).comp a.toAddMonoidHom.toIntLinearMap
    let R : O →ₗ[ℤ] (B ⟶ DB) :=
      (Linear.leftComp ℤ DB lam).comp
        ((dualAdd).toIntLinearMap.comp (a.toAddMonoidHom.toIntLinearMap.comp (tauO).linear))
    have eqMaps : L = R := by
      apply (basisO).ext
      intro k
      exact h k
    intro x
    exact DFunLike.congr_fun eqMaps x

/-- Explicit finite Rosati equations in the endomorphism tuple coordinates. -/
def IntegralRosatiTupleEquations
    (r : IntegralActionSolutions basisO B) (lam : B ⟶ DB) : Prop :=
  ∀ k, r.val k ≫ lam = lam ≫ dualInt (∑ j, (basisO).repr (tauO (basisO k)) j • r.val j)

include additivity in
/-- Reconstruction identifies the tuple equations with all actual order equations. -/
theorem integralRosatiEquations_reconstruct_iff
    (r : IntegralActionSolutions basisO B) (lam : B ⟶ DB) :
    IntegralRosatiEquations D C preservation composition unitCoherence associativity
      comparison symmetry stability B hB MB evaluationB geometryB
      ((integralActionEquiv basisO B).symm r) lam ↔
      IntegralRosatiTupleEquations D C preservation composition unitCoherence associativity
        comparison symmetry stability B hB MB evaluationB geometryB r lam := by
  rw [integralRosatiEquations_iff_basis D C preservation composition unitCoherence
    associativity comparison symmetry stability B hB additivity MB evaluationB geometryB]
  unfold IntegralRosatiBasisEquations IntegralRosatiTupleEquations
  simp_rw [integralActionEquiv_symm_apply_basis, integralActionEquiv_symm_apply]

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel

import Langlands.Shimura.PEL.HarrisIntegralOrderActions
import Langlands.Shimura.PEL.HarrisPolarizedWeilClasses

/-! # Finite Rosati equations for the actual Harris integral order -/

noncomputable section

open CategoryTheory AlgebraicGeometry Module

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
local notation "dual0" => dualHom0 preservation composition unitCoherence associativity
  comparison symmetry stability hB hB additivity MB evaluationB MB evaluationB geometryB geometryB
local notation "dualInt" => dualAbelianSchemeMapFromEvaluation hB geometryB preservation MB
  evaluationB stability composition unitCoherence associativity comparison symmetry
  hB geometryB MB evaluationB
local notation "O" => D.harrisHodgePELIntegralOrder C
local notation "basisO" => D.harrisHodgePELIntegralBasis C
local notation "tauO" => D.harrisHodgePELIntegralInvolution C
local notation "Compatible" => IsInvolutionCompatible preservation composition unitCoherence
  associativity comparison symmetry stability hB additivity MB evaluationB geometryB

/-- Actual integral equations on the finite basis of the positive Harris order. -/
def IntegralRosatiBasisEquations (a : O →+* CategoryTheory.End B) (lam : B ⟶ DB) : Prop :=
  ∀ k, a (basisO k) ≫ lam = lam ≫ dualInt (a (tauO (basisO k)))

/-- The corresponding equations in the actual rational Hom group. -/
def RationalRosatiBasisEquations (a : O →+* CategoryTheory.End B) (lam : Hom0 B DB) : Prop :=
  ∀ k, comp0 B B DB (Rationalization.ofEnd B (a (basisO k))) lam =
    comp0 B DB DB lam (dual0 (Rationalization.ofEnd B (a (tauO (basisO k)))))

/-- Full rational compatibility is equivalent to these finitely many rational equations. -/
theorem rationalAction_involutionCompatible_iff
    (a : O →+* CategoryTheory.End B) (lam : Hom0 B DB) :
    letI := auxiliaryStarRing D C
    Compatible (D.harrisHodgePELRationalAction C B a).toRingHom lam ↔
      RationalRosatiBasisEquations D C preservation composition unitCoherence associativity
        comparison symmetry stability B hB additivity MB evaluationB geometryB a lam := by
  let _ := auxiliaryStarRing D C
  let g := D.harrisHodgePELRationalAction C B a
  have onOrder (x : O) : g (x : A) = Rationalization.ofEnd B (a x) :=
    D.harrisHodgePELRationalAction_coe C B a x
  have starOrder (x : O) : star (x : A) = (tauO x : A) := rfl
  constructor
  · intro h k
    have hk := h (basisO k : A)
    change comp0 B B DB (g (basisO k : A)) lam =
      comp0 B DB DB lam (dual0 (g (star (basisO k : A)))) at hk
    simpa only [starOrder, onOrder] using hk
  · intro h
    let L : A →ₗ[ℚ] Hom0 B DB := ((comp0 B B DB).flip lam).comp g.toLinearMap
    let R : A →ₗ[ℚ] Hom0 B DB :=
      ((comp0 B DB DB) lam).comp
        ((dual0).comp (g.toLinearMap.comp
          (D.harrisHodgePELAlgebra C).toSecondKindInvolution.rationalInvolution.linear))
    have eqMaps : L = R := by
      apply ((basisO).extendOfIsLattice (M := (O).toSubmodule) ℚ).ext
      intro k
      change comp0 B B DB (g ((basisO).extendOfIsLattice (M := (O).toSubmodule) ℚ k)) lam =
        comp0 B DB DB lam (dual0 (g
          ((D.harrisHodgePELAlgebra C).toSecondKindInvolution.rationalInvolution
            ((basisO).extendOfIsLattice (M := (O).toSubmodule) ℚ k))))
      simp only [Basis.extendOfIsLattice_apply]
      change comp0 B B DB (g (basisO k : A)) lam =
        comp0 B DB DB lam (dual0 (g (star (basisO k : A))))
      simpa only [starOrder, onOrder] using h k
    intro x
    exact DFunLike.congr_fun eqMaps x

/-- Rationalization sends every finite actual equation to its rational counterpart. -/
theorem IntegralRosatiBasisEquations.rationalize
    (a : O →+* CategoryTheory.End B) (lam : B ⟶ DB)
    (h : IntegralRosatiBasisEquations D C preservation composition unitCoherence associativity
      comparison symmetry stability B hB MB evaluationB geometryB a lam) :
    RationalRosatiBasisEquations D C preservation composition unitCoherence associativity
      comparison symmetry stability B hB additivity MB evaluationB geometryB a (homToHom0 lam) := by
  intro k
  change comp0 B B DB (homToHom0 (a (basisO k))) (homToHom0 lam) =
    comp0 B DB DB (homToHom0 lam) (dual0 (homToHom0 (a (tauO (basisO k)))))
  rw [dualHom0_homToHom0, comp0_homToHom0, comp0_homToHom0]
  exact congrArg (fun f : B ⟶ DB => homToHom0 f) (h k)

/-- Finite actual Rosati equations imply the exact published rational compatibility. -/
theorem rationalAction_involutionCompatible_of_integralBasis
    (a : O →+* CategoryTheory.End B) (lam : B ⟶ DB)
    (h : IntegralRosatiBasisEquations D C preservation composition unitCoherence associativity
      comparison symmetry stability B hB MB evaluationB geometryB a lam) :
    letI := auxiliaryStarRing D C
    Compatible (D.harrisHodgePELRationalAction C B a).toRingHom (homToHom0 lam) := by
  let _ := auxiliaryStarRing D C
  exact (rationalAction_involutionCompatible_iff D C preservation composition unitCoherence associativity
    comparison symmetry stability B hB additivity MB evaluationB geometryB a (homToHom0 lam)).2
      (IntegralRosatiBasisEquations.rationalize D C preservation composition unitCoherence
        associativity comparison symmetry stability B hB additivity MB evaluationB geometryB
        a lam h)

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel

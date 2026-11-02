import Langlands.Shimura.PEL.HarrisIntegralRosatiEquations
import Langlands.AbelianScheme.RelativeIntegralActionComparison
import Langlands.AlgebraicGeometry.Picard.DualAbelianBaseChangeCoherence

/-! # Integral Harris Rosati equations under actual pullback comparisons -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

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

section Transport

variable {S : Scheme.{s}} {B B' : Langlands.AbelianScheme S}
    (hB : HasDualScheme B)
    (MB : LineBundle ((relativeSpace B.X.hom).obj (dualScheme B hB)))
    (evaluationB : tensorObj (poincareFamily B hB).obj.carrier MB.obj ≅
      structureSheaf ((relativeSpace B.X.hom).obj (dualScheme B hB)))
    (geometryB : DualSchemeGeometry B hB)
    (hB' : HasDualScheme B')
    (MB' : LineBundle ((relativeSpace B'.X.hom).obj (dualScheme B' hB')))
    (evaluationB' : tensorObj (poincareFamily B' hB').obj.carrier MB'.obj ≅
      structureSheaf ((relativeSpace B'.X.hom).obj (dualScheme B' hB')))
    (geometryB' : DualSchemeGeometry B' hB')

local notation "DB" => dualAbelianSchemeFromEvaluation B hB geometryB preservation MB
  evaluationB stability composition unitCoherence associativity comparison symmetry
local notation "DB'" => dualAbelianSchemeFromEvaluation B' hB' geometryB' preservation MB'
  evaluationB' stability composition unitCoherence associativity comparison symmetry
local notation "dB" => dualAbelianSchemeMapFromEvaluation hB geometryB preservation MB
  evaluationB stability composition unitCoherence associativity comparison symmetry
  hB geometryB MB evaluationB
local notation "dB'" => dualAbelianSchemeMapFromEvaluation hB' geometryB' preservation MB'
  evaluationB' stability composition unitCoherence associativity comparison symmetry
  hB' geometryB' MB' evaluationB'
local notation "dForward" => dualAbelianSchemeMapFromEvaluation hB' geometryB' preservation MB'
  evaluationB' stability composition unitCoherence associativity comparison symmetry
  hB geometryB MB evaluationB
local notation "dBackward" => dualAbelianSchemeMapFromEvaluation hB geometryB preservation MB
  evaluationB stability composition unitCoherence associativity comparison symmetry
  hB' geometryB' MB' evaluationB'
local notation "O" => D.harrisHodgePELIntegralOrder C
local notation "tauO" => D.harrisHodgePELIntegralInvolution C
local notation "basisO" => D.harrisHodgePELIntegralBasis C

/-- Pull an actual map to the chosen dual through an actual abelian-scheme comparison. -/
def integralRosatiComparisonMap (c : B' ≅ B) (lam : B ⟶ DB) : B' ⟶ DB' :=
  c.hom ≫ lam ≫ dForward c.hom

private theorem rosatiComparisonDual_intertwines
    (c : B' ≅ B) (u : CategoryTheory.End B) (u' : CategoryTheory.End B')
    (hu : u' ≫ c.hom = c.hom ≫ u) :
    dB u ≫ dForward c.hom = dForward c.hom ≫ dB' u' := by
  have h := congrArg dForward hu
  rw [dualAbelianSchemeMapFromEvaluation_comp hB' geometryB' preservation MB' evaluationB'
    stability composition unitCoherence associativity comparison symmetry
    hB' geometryB' MB' evaluationB' hB geometryB MB evaluationB,
    dualAbelianSchemeMapFromEvaluation_comp hB' geometryB' preservation MB' evaluationB'
    stability composition unitCoherence associativity comparison symmetry
    hB geometryB MB evaluationB hB geometryB MB evaluationB] at h
  exact h.symm

/-- Each actual Rosati equation is invariant under an equivariant actual comparison. -/
theorem integralRosatiComparison_equation_iff
    (c : B' ≅ B)
    (a : O →+* CategoryTheory.End B) (a' : O →+* CategoryTheory.End B')
    (ha : ∀ x : O, a' x ≫ c.hom = c.hom ≫ a x) (lam : B ⟶ DB) (x : O) :
    a' x ≫ integralRosatiComparisonMap preservation composition unitCoherence associativity
        comparison symmetry stability hB MB evaluationB geometryB hB' MB' evaluationB'
        geometryB' c lam =
      integralRosatiComparisonMap preservation composition unitCoherence associativity
        comparison symmetry stability hB MB evaluationB geometryB hB' MB' evaluationB'
        geometryB' c lam ≫ dB' (a' (tauO x)) ↔
      a x ≫ lam = lam ≫ dB (a (tauO x)) := by
  let dc := dualAbelianSchemeIsoFromEvaluation preservation stability composition
    unitCoherence associativity comparison symmetry B' hB' geometryB' MB' evaluationB'
    hB geometryB MB evaluationB c
  have hl :
      a' x ≫ integralRosatiComparisonMap preservation composition unitCoherence associativity
        comparison symmetry stability hB MB evaluationB geometryB hB' MB' evaluationB'
        geometryB' c lam =
      (c.hom ≫ (a x ≫ lam)) ≫ dc.hom := by
    simpa only [integralRosatiComparisonMap, dc, dualAbelianSchemeIsoFromEvaluation, Category.assoc] using
      congrArg (fun k => k ≫ lam ≫ dForward c.hom) (ha x)
  have hr :
      integralRosatiComparisonMap preservation composition unitCoherence associativity
        comparison symmetry stability hB MB evaluationB geometryB hB' MB' evaluationB'
        geometryB' c lam ≫ dB' (a' (tauO x)) =
      (c.hom ≫ (lam ≫ dB (a (tauO x)))) ≫ dc.hom := by
    dsimp only [integralRosatiComparisonMap, dc, dualAbelianSchemeIsoFromEvaluation]
    simp only [Category.assoc]
    rw [← rosatiComparisonDual_intertwines preservation composition unitCoherence associativity
      comparison symmetry stability hB MB evaluationB geometryB hB' MB' evaluationB'
      geometryB' c (a (tauO x)) (a' (tauO x)) (ha (tauO x))]
  rw [hl, hr]
  exact (cancel_mono dc.hom).trans (cancel_epi c.hom)

/-- The same actual comparison preserves the finite Harris basis equations. -/
theorem integralRosatiBasisEquations_comparison_iff
    (c : B' ≅ B)
    (a : O →+* CategoryTheory.End B) (a' : O →+* CategoryTheory.End B')
    (ha : ∀ x : O, a' x ≫ c.hom = c.hom ≫ a x) (lam : B ⟶ DB) :
    IntegralRosatiBasisEquations D C preservation composition unitCoherence associativity
      comparison symmetry stability B' hB' MB' evaluationB' geometryB' a'
      (integralRosatiComparisonMap preservation composition unitCoherence associativity
        comparison symmetry stability hB MB evaluationB geometryB hB' MB' evaluationB'
        geometryB' c lam) ↔
    IntegralRosatiBasisEquations D C preservation composition unitCoherence associativity
      comparison symmetry stability B hB MB evaluationB geometryB a lam := by
  exact forall_congr' fun k =>
    integralRosatiComparison_equation_iff D C preservation composition unitCoherence associativity
      comparison symmetry stability hB MB evaluationB geometryB hB' MB' evaluationB'
      geometryB' c a a' ha lam (basisO k)

/-- The comparison also preserves the equations on the entire integral Harris order. -/
theorem integralRosatiEquations_comparison_iff
    (c : B' ≅ B)
    (a : O →+* CategoryTheory.End B) (a' : O →+* CategoryTheory.End B')
    (ha : ∀ x : O, a' x ≫ c.hom = c.hom ≫ a x) (lam : B ⟶ DB) :
    IntegralRosatiEquations D C preservation composition unitCoherence associativity
      comparison symmetry stability B' hB' MB' evaluationB' geometryB' a'
      (integralRosatiComparisonMap preservation composition unitCoherence associativity
        comparison symmetry stability hB MB evaluationB geometryB hB' MB' evaluationB'
        geometryB' c lam) ↔
    IntegralRosatiEquations D C preservation composition unitCoherence associativity
      comparison symmetry stability B hB MB evaluationB geometryB a lam := by
  exact forall_congr' fun x =>
    integralRosatiComparison_equation_iff D C preservation composition unitCoherence associativity
      comparison symmetry stability hB MB evaluationB geometryB hB' MB' evaluationB'
      geometryB' c a a' ha lam x

end Transport

section RelativePullback

variable {S : Scheme.{s}} (B : Langlands.AbelianScheme S)
    {T T' : Over S} (f : T' ⟶ T)
    (hStep : HasDualScheme ((baseChange f.left).obj ((baseChange T.hom).obj B)))
    (MStep : LineBundle
      ((relativeSpace ((baseChange f.left).obj ((baseChange T.hom).obj B)).X.hom).obj
        (dualScheme ((baseChange f.left).obj ((baseChange T.hom).obj B)) hStep)))
    (evaluationStep : tensorObj
      (poincareFamily ((baseChange f.left).obj ((baseChange T.hom).obj B)) hStep).obj.carrier
      MStep.obj ≅
      structureSheaf
        ((relativeSpace ((baseChange f.left).obj ((baseChange T.hom).obj B)).X.hom).obj
          (dualScheme ((baseChange f.left).obj ((baseChange T.hom).obj B)) hStep)))
    (geometryStep : DualSchemeGeometry
      ((baseChange f.left).obj ((baseChange T.hom).obj B)) hStep)
    (hDirect : HasDualScheme ((baseChange T'.hom).obj B))
    (MDirect : LineBundle
      ((relativeSpace ((baseChange T'.hom).obj B).X.hom).obj
        (dualScheme ((baseChange T'.hom).obj B) hDirect)))
    (evaluationDirect : tensorObj
      (poincareFamily ((baseChange T'.hom).obj B) hDirect).obj.carrier MDirect.obj ≅
      structureSheaf
        ((relativeSpace ((baseChange T'.hom).obj B).X.hom).obj
          (dualScheme ((baseChange T'.hom).obj B) hDirect)))
    (geometryDirect : DualSchemeGeometry ((baseChange T'.hom).obj B) hDirect)

local notation "BStep" => Functor.obj (baseChange f.left) (Functor.obj (baseChange T.hom) B)
local notation "BDirect" => Functor.obj (baseChange T'.hom) B
local notation "DStep" => dualAbelianSchemeFromEvaluation BStep hStep geometryStep
  preservation MStep evaluationStep stability composition unitCoherence associativity
  comparison symmetry
local notation "DDirect" => dualAbelianSchemeFromEvaluation BDirect hDirect geometryDirect
  preservation MDirect evaluationDirect stability composition unitCoherence associativity
  comparison symmetry
local notation "O" => D.harrisHodgePELIntegralOrder C

/-- Transport from the successive pullback to the original direct family. -/
def relativeIntegralRosatiComparisonMap (lam : BStep ⟶ DStep) : BDirect ⟶ DDirect :=
  integralRosatiComparisonMap preservation composition unitCoherence associativity
    comparison symmetry stability hStep MStep evaluationStep geometryStep
    hDirect MDirect evaluationDirect geometryDirect (relativeBaseChangeComparisonIso B f) lam

/-- The actual canonical comparison preserves the finite Harris Rosati equations. -/
theorem integralRosatiBasisEquations_relativeComparison_iff
    (a : O →+* CategoryTheory.End ((baseChange T.hom).obj B))
    (lam : BStep ⟶ DStep) :
    IntegralRosatiBasisEquations D C preservation composition unitCoherence associativity
      comparison symmetry stability BDirect hDirect MDirect evaluationDirect geometryDirect
      ((relativeEndRestrict B f).comp a)
      (relativeIntegralRosatiComparisonMap preservation composition unitCoherence associativity
        comparison symmetry stability B f hStep MStep evaluationStep geometryStep
        hDirect MDirect evaluationDirect geometryDirect lam) ↔
    IntegralRosatiBasisEquations D C preservation composition unitCoherence associativity
      comparison symmetry stability BStep hStep MStep evaluationStep geometryStep
      (baseChangeOrderAction f.left ((baseChange T.hom).obj B) a) lam := by
  exact integralRosatiBasisEquations_comparison_iff D C preservation composition
    unitCoherence associativity comparison symmetry stability
    hStep MStep evaluationStep geometryStep hDirect MDirect evaluationDirect geometryDirect
    (relativeBaseChangeComparisonIso B f)
    (baseChangeOrderAction f.left ((baseChange T.hom).obj B) a)
    ((relativeEndRestrict B f).comp a)
    (fun x => relativeEndRestrict_comparison_intertwines B f (a x)) lam

/-- The actual canonical comparison preserves the equations on every order element. -/
theorem integralRosatiEquations_relativeComparison_iff
    (a : O →+* CategoryTheory.End ((baseChange T.hom).obj B))
    (lam : BStep ⟶ DStep) :
    IntegralRosatiEquations D C preservation composition unitCoherence associativity
      comparison symmetry stability BDirect hDirect MDirect evaluationDirect geometryDirect
      ((relativeEndRestrict B f).comp a)
      (relativeIntegralRosatiComparisonMap preservation composition unitCoherence associativity
        comparison symmetry stability B f hStep MStep evaluationStep geometryStep
        hDirect MDirect evaluationDirect geometryDirect lam) ↔
    IntegralRosatiEquations D C preservation composition unitCoherence associativity
      comparison symmetry stability BStep hStep MStep evaluationStep geometryStep
      (baseChangeOrderAction f.left ((baseChange T.hom).obj B) a) lam := by
  exact integralRosatiEquations_comparison_iff D C preservation composition
    unitCoherence associativity comparison symmetry stability
    hStep MStep evaluationStep geometryStep hDirect MDirect evaluationDirect geometryDirect
    (relativeBaseChangeComparisonIso B f)
    (baseChangeOrderAction f.left ((baseChange T.hom).obj B) a)
    ((relativeEndRestrict B f).comp a)
    (fun x => relativeEndRestrict_comparison_intertwines B f (a x)) lam

end RelativePullback

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel

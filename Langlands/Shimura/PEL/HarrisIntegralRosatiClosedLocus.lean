import Langlands.Shimura.PEL.HarrisIntegralRosatiBaseChange
import Langlands.AlgebraicGeometry.Picard.DualMapFiniteEqualityLocus

/-! # An unconditional closed locus for the actual finite Harris Rosati equations -/

noncomputable section

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Module Opposite

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
    {S : Scheme.{s}}
    (B : Langlands.AbelianScheme S)
    (hB : HasDualScheme B)
    (MB : LineBundle ((relativeSpace B.X.hom).obj (dualScheme B hB)))
    (evaluationB : tensorObj (poincareFamily B hB).obj.carrier MB.obj ≅
      structureSheaf ((relativeSpace B.X.hom).obj (dualScheme B hB)))
    (geometryB : DualSchemeGeometry B hB)

local notation "DB" => dualAbelianSchemeFromEvaluation B hB geometryB preservation MB
  evaluationB stability composition unitCoherence associativity comparison symmetry
local notation "dualInt" => dualAbelianSchemeMapFromEvaluation hB geometryB preservation MB
  evaluationB stability composition unitCoherence associativity comparison symmetry
  hB geometryB MB evaluationB
local notation "O" => D.harrisHodgePELIntegralOrder C
local notation "basisO" => D.harrisHodgePELIntegralBasis C
local notation "tauO" => D.harrisHodgePELIntegralInvolution C

variable
    (a : D.harrisHodgePELIntegralOrder C →+* CategoryTheory.End B)
    (lam : B ⟶ dualAbelianSchemeFromEvaluation B hB geometryB preservation MB
      evaluationB stability composition unitCoherence associativity comparison symmetry)

/-- The closed locus of the finite actual Harris Rosati equations, constructed
from equality loci for maps into the chosen dual. -/
abbrev integralRosatiClosedLocus : Over S :=
  DualMapEquality.finiteLocus B hB
    (fun k => (groupHom (a (basisO k) ≫ lam)).hom.hom)
    (fun k => (groupHom (lam ≫ dualInt (a (tauO (basisO k))))).hom.hom)

/-- The actual Rosati locus is closed without a supplied relative Hom representative. -/
instance integralRosatiClosedLocus_isClosedImmersion :
    IsClosedImmersion (integralRosatiClosedLocus D C preservation composition unitCoherence
      associativity comparison symmetry stability B hB MB evaluationB geometryB a lam).hom :=
  inferInstanceAs (IsClosedImmersion
    (DualMapEquality.finiteLocus B hB
      (fun k => (groupHom (a (basisO k) ≫ lam)).hom.hom)
      (fun k => (groupHom (lam ≫ dualInt (a (tauO (basisO k))))).hom.hom)).hom)

instance integralRosatiClosedLocus_isLocallyNoetherian [IsLocallyNoetherian S] :
    IsLocallyNoetherian (integralRosatiClosedLocus D C preservation composition unitCoherence
      associativity comparison symmetry stability B hB MB evaluationB geometryB a lam).left :=
  LocallyOfFiniteType.isLocallyNoetherian
    (integralRosatiClosedLocus D C preservation composition unitCoherence associativity
      comparison symmetry stability B hB MB evaluationB geometryB a lam).hom

/-- On every scheme test, the chosen closed locus detects equality of the actual
base-changed homomorphisms in the finite Rosati equations. -/
theorem integralRosatiClosedLocus_nonempty_iff_pullback (T : Over S) :
    Nonempty (T ⟶ integralRosatiClosedLocus D C preservation composition unitCoherence
      associativity comparison symmetry stability B hB MB evaluationB geometryB a lam) ↔
      ∀ k, (baseChange T.hom).map (a (basisO k) ≫ lam) =
        (baseChange T.hom).map (lam ≫ dualInt (a (tauO (basisO k)))) := by
  rw [DualMapEquality.finiteLocus_nonempty_iff]
  apply forall_congr'
  intro k
  constructor
  · intro hk
    apply Additive.toMul.injective
    apply Grp.hom_ext
    exact hk
  · intro hk
    exact congrArg (fun f => (groupHom f).hom.hom) hk

section Test

variable
    (universality : PicardZeroUniversalBaseChangeStatement.{s})
    (compatibility : DualAbelianBaseChangeStatement.{s})
    (T : Over S)
    (hT : HasDualScheme ((baseChange T.hom).obj B))
    (MT : LineBundle ((relativeSpace ((baseChange T.hom).obj B).X.hom).obj
      (dualScheme ((baseChange T.hom).obj B) hT)))
    (evaluationT : tensorObj (poincareFamily ((baseChange T.hom).obj B) hT).obj.carrier
      MT.obj ≅ structureSheaf ((relativeSpace ((baseChange T.hom).obj B).X.hom).obj
        (dualScheme ((baseChange T.hom).obj B) hT)))
    (geometryT : DualSchemeGeometry ((baseChange T.hom).obj B) hT)

local notation "beta" => dualAbelianBaseChangeIso preservation stability composition
  unitCoherence associativity comparison symmetry universality compatibility T.hom B
  hB geometryB MB evaluationB hT geometryT MT evaluationT
local notation "pullLam" => dualAbelianBaseChangeMap preservation stability composition
  unitCoherence associativity comparison symmetry universality compatibility T.hom B
  hB geometryB MB evaluationB hT geometryT MT evaluationT
local notation "dualIntT" => dualAbelianSchemeMapFromEvaluation hT geometryT preservation MT
  evaluationT stability composition unitCoherence associativity comparison symmetry
  hT geometryT MT evaluationT

private theorem integralRosatiClosedPullbackEquation_iff (f g : CategoryTheory.End B) :
    (baseChange T.hom).map (f ≫ lam) =
        (baseChange T.hom).map (lam ≫ dualInt g) ↔
      (baseChange T.hom).map f ≫ pullLam lam =
        pullLam lam ≫ dualIntT ((baseChange T.hom).map g) := by
  have leftEq : (baseChange T.hom).map (f ≫ lam) ≫ (beta).hom =
      (baseChange T.hom).map f ≫ pullLam lam := by
    rw [Functor.map_comp, Category.assoc]
    rfl
  have rightEq : (baseChange T.hom).map (lam ≫ dualInt g) ≫ (beta).hom =
      pullLam lam ≫ dualIntT ((baseChange T.hom).map g) := by
    rw [Functor.map_comp, Category.assoc,
      dualAbelianBaseChangeNaturality preservation stability composition unitCoherence
        associativity comparison symmetry universality compatibility S T.left T.hom B B
        hB geometryB MB evaluationB hB geometryB MB evaluationB
        hT geometryT MT evaluationT hT geometryT MT evaluationT]
    exact (Category.assoc _ _ _).symm
  exact (cancel_mono (beta).hom).symm.trans (by rw [leftEq, rightEq])

/-- Factoring through the actual locus is equivalent to the published finite Rosati predicate. -/
theorem integralRosatiClosedLocus_nonempty_iff_basis :
    Nonempty (T ⟶ integralRosatiClosedLocus D C preservation composition unitCoherence
      associativity comparison symmetry stability B hB MB evaluationB geometryB a lam) ↔
    IntegralRosatiBasisEquations D C preservation composition unitCoherence associativity
      comparison symmetry stability ((baseChange T.hom).obj B) hT MT evaluationT geometryT
      (baseChangeOrderAction T.hom B a) (pullLam lam) := by
  rw [integralRosatiClosedLocus_nonempty_iff_pullback]
  unfold IntegralRosatiBasisEquations
  exact forall_congr' fun k =>
    integralRosatiClosedPullbackEquation_iff preservation composition unitCoherence associativity
      comparison symmetry stability B hB MB evaluationB geometryB lam
      universality compatibility T hT MT evaluationT geometryT
      (a (basisO k)) (a (tauO (basisO k)))

/-- With actual dual additivity, the same locus detects every element of the integral order. -/
theorem integralRosatiClosedLocus_nonempty_iff
    (additivityT : DualSchemeMapAdditivity preservation stability
      ((baseChange T.hom).obj B) ((baseChange T.hom).obj B) hT hT) :
    Nonempty (T ⟶ integralRosatiClosedLocus D C preservation composition unitCoherence
      associativity comparison symmetry stability B hB MB evaluationB geometryB a lam) ↔
    IntegralRosatiEquations D C preservation composition unitCoherence associativity
      comparison symmetry stability ((baseChange T.hom).obj B) hT MT evaluationT geometryT
      (baseChangeOrderAction T.hom B a) (pullLam lam) := by
  rw [integralRosatiEquations_iff_basis D C preservation composition unitCoherence
    associativity comparison symmetry stability ((baseChange T.hom).obj B) hT
    additivityT MT evaluationT geometryT]
  exact integralRosatiClosedLocus_nonempty_iff_basis D C preservation composition unitCoherence
    associativity comparison symmetry stability B hB MB evaluationB geometryB a lam
    universality compatibility T hT MT evaluationT geometryT

end Test

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel

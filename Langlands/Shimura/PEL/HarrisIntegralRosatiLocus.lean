import Langlands.Shimura.PEL.HarrisIntegralRosatiBaseChange
import Langlands.GroupScheme.Cartier.RelativeHomEquationLocus

/-! # The actual finite integral Harris Rosati locus -/

noncomputable section

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Module Opposite

universe s

namespace Langlands.Shimura.PEL.HarrisPolarizedWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.GroupScheme.Cartier

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
    {S : Scheme.{s}} [IsLocallyNoetherian S]
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

variable (H : Over S)
    (e : (locallyNoetherianTestInclusion S).op ⋙
        relativeHomFunctor B.toCommGroupScheme
          (dualAbelianSchemeFromEvaluation B hB geometryB preservation MB
            evaluationB stability composition unitCoherence associativity comparison
            symmetry).toCommGroupScheme ⋙ forget AddCommGrpCat.{s} ≅
      (locallyNoetherianTestInclusion S).op ⋙ yoneda.obj H)
    (a : D.harrisHodgePELIntegralOrder C →+* CategoryTheory.End B)
    (lam : B ⟶ dualAbelianSchemeFromEvaluation B hB geometryB preservation MB
      evaluationB stability composition unitCoherence associativity comparison symmetry)

/-- The actual equalizer of the finite Harris Rosati equations for an integral action family. -/
abbrev integralRosatiLocus : Over S :=
  relativeHomEquationLocus B.toCommGroupScheme (DB).toCommGroupScheme H e
    (fun k => commHom (a (basisO k) ≫ lam))
    (fun k => commHom (lam ≫ dualInt (a (tauO (basisO k)))))


/-- The finite Rosati locus is a closed subscheme of the action family's base. -/
instance integralRosatiLocus_isClosedImmersion [IsSeparated H.hom] :
    IsClosedImmersion (integralRosatiLocus D C preservation composition unitCoherence
      associativity comparison symmetry stability B hB MB evaluationB geometryB H e a lam).hom :=
  inferInstanceAs (IsClosedImmersion
    (relativeHomEquationLocus B.toCommGroupScheme (DB).toCommGroupScheme H e
      (fun k => commHom (a (basisO k) ≫ lam))
      (fun k => commHom (lam ≫ dualInt (a (tauO (basisO k)))))).hom)

instance integralRosatiLocus_isLocallyNoetherian [IsSeparated H.hom] :
    IsLocallyNoetherian (integralRosatiLocus D C preservation composition unitCoherence
      associativity comparison symmetry stability B hB MB evaluationB geometryB H e a lam).left :=
  LocallyOfFiniteType.isLocallyNoetherian
    (integralRosatiLocus D C preservation composition unitCoherence associativity comparison
      symmetry stability B hB MB evaluationB geometryB H e a lam).hom

section Test

variable
    (universality : PicardZeroUniversalBaseChangeStatement.{s})
    (compatibility : DualAbelianBaseChangeStatement.{s})
    (T : ObjectProperty.FullSubcategory (fun T : Over S => IsLocallyNoetherian T.left))
    (hT : HasDualScheme ((baseChange T.obj.hom).obj B))
    (MT : LineBundle ((relativeSpace ((baseChange T.obj.hom).obj B).X.hom).obj
      (dualScheme ((baseChange T.obj.hom).obj B) hT)))
    (evaluationT : tensorObj (poincareFamily ((baseChange T.obj.hom).obj B) hT).obj.carrier
      MT.obj ≅ structureSheaf ((relativeSpace ((baseChange T.obj.hom).obj B).X.hom).obj
        (dualScheme ((baseChange T.obj.hom).obj B) hT)))
    (geometryT : DualSchemeGeometry ((baseChange T.obj.hom).obj B) hT)

local notation "beta" => dualAbelianBaseChangeIso preservation stability composition
  unitCoherence associativity comparison symmetry universality compatibility T.obj.hom B
  hB geometryB MB evaluationB hT geometryT MT evaluationT
local notation "pullLam" => dualAbelianBaseChangeMap preservation stability composition
  unitCoherence associativity comparison symmetry universality compatibility T.obj.hom B
  hB geometryB MB evaluationB hT geometryT MT evaluationT
local notation "dualIntT" => dualAbelianSchemeMapFromEvaluation hT geometryT preservation MT
  evaluationT stability composition unitCoherence associativity comparison symmetry
  hT geometryT MT evaluationT

omit [IsLocallyNoetherian S] in
private theorem integralRosatiPullbackEquation_iff (f g : CategoryTheory.End B) :
    (baseChange T.obj.hom).map (f ≫ lam) =
        (baseChange T.obj.hom).map (lam ≫ dualInt g) ↔
      (baseChange T.obj.hom).map f ≫ pullLam lam =
        pullLam lam ≫ dualIntT ((baseChange T.obj.hom).map g) := by
  have leftEq : (baseChange T.obj.hom).map (f ≫ lam) ≫ (beta).hom =
      (baseChange T.obj.hom).map f ≫ pullLam lam := by
    rw [Functor.map_comp, Category.assoc]
    rfl
  have rightEq : (baseChange T.obj.hom).map (lam ≫ dualInt g) ≫ (beta).hom =
      pullLam lam ≫ dualIntT ((baseChange T.obj.hom).map g) := by
    rw [Functor.map_comp, Category.assoc,
      dualAbelianBaseChangeNaturality preservation stability composition unitCoherence
        associativity comparison symmetry universality compatibility S T.obj.left T.obj.hom B B
        hB geometryB MB evaluationB hB geometryB MB evaluationB
        hT geometryT MT evaluationT hT geometryT MT evaluationT]
    exact (Category.assoc _ _ _).symm
  exact (cancel_mono (beta).hom).symm.trans (by rw [leftEq, rightEq])

/-- Factoring through the actual locus is equivalent to the published finite Rosati predicate. -/
theorem integralRosatiLocus_nonempty_iff_basis :
    Nonempty (T.obj ⟶ integralRosatiLocus D C preservation composition unitCoherence
      associativity comparison symmetry stability B hB MB evaluationB geometryB H e a lam) ↔
    IntegralRosatiBasisEquations D C preservation composition unitCoherence associativity
      comparison symmetry stability ((baseChange T.obj.hom).obj B) hT MT evaluationT geometryT
      (baseChangeOrderAction T.obj.hom B a) (pullLam lam) := by
  rw [relativeHomEquationLocus_nonempty_iff]
  unfold IntegralRosatiBasisEquations
  exact forall_congr' fun k =>
    integralRosatiPullbackEquation_iff preservation composition unitCoherence associativity
      comparison symmetry stability B hB MB evaluationB geometryB lam
      universality compatibility T hT MT evaluationT geometryT
      (a (basisO k)) (a (tauO (basisO k)))

/-- With actual dual additivity, the same locus detects every element of the integral order. -/
theorem integralRosatiLocus_nonempty_iff
    (additivityT : DualSchemeMapAdditivity preservation stability
      ((baseChange T.obj.hom).obj B) ((baseChange T.obj.hom).obj B) hT hT) :
    Nonempty (T.obj ⟶ integralRosatiLocus D C preservation composition unitCoherence
      associativity comparison symmetry stability B hB MB evaluationB geometryB H e a lam) ↔
    IntegralRosatiEquations D C preservation composition unitCoherence associativity
      comparison symmetry stability ((baseChange T.obj.hom).obj B) hT MT evaluationT geometryT
      (baseChangeOrderAction T.obj.hom B a) (pullLam lam) := by
  rw [integralRosatiEquations_iff_basis D C preservation composition unitCoherence
    associativity comparison symmetry stability ((baseChange T.obj.hom).obj B) hT
    additivityT MT evaluationT geometryT]
  exact integralRosatiLocus_nonempty_iff_basis D C preservation composition unitCoherence
    associativity comparison symmetry stability B hB MB evaluationB geometryB H e a lam
    universality compatibility T hT MT evaluationT geometryT

end Test

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel

import Langlands.AbelianScheme.Tate.WeilIntegralPolarizationComparison
import Langlands.AlgebraicGeometry.Picard.DualAbelianBaseChangeNaturalityProof

/-! # Base change of exact integral polarization cross-multiples -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
  (stability : PicardZeroPullbackStatement.{u})
  (composition : PullbackTensorCompositionStatement.{u})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
  (symmetry : PullbackTensorSymmetryStatement.{u})
  (universality : PicardZeroUniversalBaseChangeStatement.{u})
  (compatibility : DualAbelianBaseChangeStatement.{u})
  {S S' : Scheme.{u}} (b : S' ⟶ S) (A B : AbelianScheme S)
  (hA : HasDualScheme A) (geometryA : DualSchemeGeometry A hA)
  (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
    structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (hB : HasDualScheme B) (geometryB : DualSchemeGeometry B hB)
  (MB : LineBundle ((relativeSpace B.X.hom).obj (dualScheme B hB)))
  (evaluationB : tensorObj (poincareFamily B hB).obj.carrier MB.obj ≅
    structureSheaf ((relativeSpace B.X.hom).obj (dualScheme B hB)))
  (hA' : HasDualScheme ((baseChange b).obj A))
  (geometryA' : DualSchemeGeometry ((baseChange b).obj A) hA')
  (MA' : LineBundle ((relativeSpace ((baseChange b).obj A).X.hom).obj
    (dualScheme ((baseChange b).obj A) hA')))
  (evaluationA' : tensorObj (poincareFamily ((baseChange b).obj A) hA').obj.carrier
    MA'.obj ≅ structureSheaf ((relativeSpace ((baseChange b).obj A).X.hom).obj
      (dualScheme ((baseChange b).obj A) hA')))
  (hB' : HasDualScheme ((baseChange b).obj B))
  (geometryB' : DualSchemeGeometry ((baseChange b).obj B) hB')
  (MB' : LineBundle ((relativeSpace ((baseChange b).obj B).X.hom).obj
    (dualScheme ((baseChange b).obj B) hB')))
  (evaluationB' : tensorObj (poincareFamily ((baseChange b).obj B) hB').obj.carrier
    MB'.obj ≅ structureSheaf ((relativeSpace ((baseChange b).obj B).X.hom).obj
      (dualScheme ((baseChange b).obj B) hB')))

local notation "DA" => dualAbelianSchemeFromEvaluation A hA geometryA preservation MA
  evaluationA stability composition unitCoherence associativity comparison symmetry
local notation "DB" => dualAbelianSchemeFromEvaluation B hB geometryB preservation MB
  evaluationB stability composition unitCoherence associativity comparison symmetry
local notation "baseA" => Functor.obj (baseChange b) A
local notation "baseB" => Functor.obj (baseChange b) B
local notation "EA" => dualAbelianBaseChangeIso preservation stability composition unitCoherence
  associativity comparison symmetry universality compatibility b A
  hA geometryA MA evaluationA hA' geometryA' MA' evaluationA'
local notation "EB" => dualAbelianBaseChangeIso preservation stability composition unitCoherence
  associativity comparison symmetry universality compatibility b B
  hB geometryB MB evaluationB hB' geometryB' MB' evaluationB'
local notation "dualAB" => dualAbelianSchemeMapFromEvaluation hA geometryA preservation MA
  evaluationA stability composition unitCoherence associativity comparison symmetry
  hB geometryB MB evaluationB
local notation "dualAB'" => dualAbelianSchemeMapFromEvaluation hA' geometryA' preservation MA'
  evaluationA' stability composition unitCoherence associativity comparison symmetry
  hB' geometryB' MB' evaluationB'
local notation "pullA" => dualAbelianBaseChangeMap preservation stability composition
  unitCoherence associativity comparison symmetry universality compatibility b A
  hA geometryA MA evaluationA hA' geometryA' MA' evaluationA'
local notation "pullB" => dualAbelianBaseChangeMap preservation stability composition
  unitCoherence associativity comparison symmetry universality compatibility b B
  hB geometryB MB evaluationB hB' geometryB' MB' evaluationB'
local notation "oldPull" => integralDualPullbackHom preservation composition unitCoherence
  associativity comparison symmetry stability hA hB geometryA geometryB MA evaluationA
  MB evaluationB
local notation "changedPull" => integralDualPullbackHom preservation composition
  unitCoherence associativity comparison symmetry stability hA' hB' geometryA' geometryB'
  MA' evaluationA' MB' evaluationB'

/-- Actual integral dual pullback commutes with canonical dual base change. -/
theorem integralDualPullbackHom_baseChange (f : A ⟶ B) (lamB : B ⟶ DB) :
    pullA (oldPull f lamB) = changedPull ((baseChange b).map f) (pullB lamB) := by
  change (baseChange b).map (f ≫ lamB ≫ dualAB f) ≫ (EA).hom =
    (baseChange b).map f ≫ ((baseChange b).map lamB ≫ (EB).hom) ≫
      dualAB' ((baseChange b).map f)
  simp only [Functor.map_comp, Category.assoc]
  rw [dualAbelianBaseChangeNaturality preservation stability composition unitCoherence
    associativity comparison symmetry universality compatibility S S' b A B
    hA geometryA MA evaluationA hB geometryB MB evaluationB
    hA' geometryA' MA' evaluationA' hB' geometryB' MB' evaluationB']

/-- Transport supplied exact integral polarization data, preserving its two integers
and its prescribed rational ratio. -/
def integralDualMultipleDataBaseChange (q : ℚ) (f : A ⟶ B)
    (lamA : A ⟶ DA) (lamB : B ⟶ DB)
    (d : Rationalization.IntegralMultipleData (oldPull f lamB) lamA q) :
    Rationalization.IntegralMultipleData
      (changedPull ((baseChange b).map f) (pullB lamB)) (pullA lamA) q where
  left := d.left
  right := d.right
  left_ne_zero := d.left_ne_zero
  ratio := d.ratio
  equation := by
    have hd := congrArg (fun z : A ⟶ DA => (baseChange b).map z ≫ (EA).hom) d.equation
    have hmap : d.left • pullA (oldPull f lamB) = d.right • pullA lamA := by
      simpa only [Functor.map_zsmul, Preadditive.zsmul_comp,
        dualAbelianBaseChangeMap] using hd
    rw [integralDualPullbackHom_baseChange preservation stability composition unitCoherence
      associativity comparison symmetry universality compatibility b A B
      hA geometryA MA evaluationA hB geometryB MB evaluationB
      hA' geometryA' MA' evaluationA' hB' geometryB' MB' evaluationB'] at hmap
    exact hmap

end Langlands.AbelianScheme

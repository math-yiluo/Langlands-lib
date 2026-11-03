import Langlands.AlgebraicGeometry.Picard.DualMapAdditive
import Langlands.AbelianScheme.IntegralInverseIsogeny

/-! # Exact inverse-multiple data for actual dual homomorphisms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
  (composition : PullbackTensorCompositionStatement.{u})
  (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
  (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
  (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
  (symmetry : PullbackTensorSymmetryStatement.{u})
  (stability : PicardZeroPullbackStatement.{u})
  {S : Scheme.{u}} {A B : AbelianScheme S}
  (hA : HasDualScheme A) (hB : HasDualScheme B)
  (geometryA : DualSchemeGeometry A hA) (geometryB : DualSchemeGeometry B hB)
  (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
    structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  (MB : LineBundle ((relativeSpace B.X.hom).obj (dualScheme B hB)))
  (evaluationB : tensorObj (poincareFamily B hB).obj.carrier MB.obj ≅
    structureSheaf ((relativeSpace B.X.hom).obj (dualScheme B hB)))
  (additivityAA : DualSchemeMapAdditivity preservation stability A A hA hA)
  (additivityBB : DualSchemeMapAdditivity preservation stability B B hB hB)

local notation "DA" => dualAbelianSchemeFromEvaluation A hA geometryA preservation MA
  evaluationA stability composition unitCoherence associativity comparison symmetry
local notation "DB" => dualAbelianSchemeFromEvaluation B hB geometryB preservation MB
  evaluationB stability composition unitCoherence associativity comparison symmetry
local notation "dualAB" => dualAbelianSchemeMapFromEvaluation hA geometryA preservation MA
  evaluationA stability composition unitCoherence associativity comparison symmetry
  hB geometryB MB evaluationB
local notation "dualBA" => dualAbelianSchemeMapFromEvaluation hB geometryB preservation MB
  evaluationB stability composition unitCoherence associativity comparison symmetry
  hA geometryA MA evaluationA
local notation "dualAA" => dualAbelianSchemeMapAddHom preservation composition unitCoherence
  associativity comparison symmetry stability hA hA additivityAA MA evaluationA MA evaluationA
  geometryA geometryA
local notation "dualBB" => dualAbelianSchemeMapAddHom preservation composition unitCoherence
  associativity comparison symmetry stability hB hB additivityBB MB evaluationB MB evaluationB
  geometryB geometryB

/-- Dualize the two actual integral maps in reverse order, retaining exactly
the common nonzero integer multiplier. -/
def dualIntegralInverseData (d : Rationalization.IntegralInverseData A B) :
    Rationalization.IntegralInverseData DA DB where
  multiple := d.multiple
  multiple_ne_zero := d.multiple_ne_zero
  hom := dualBA d.inv
  inv := dualAB d.hom
  hom_inv := by
    calc
      dualBA d.inv ≫ dualAB d.hom = dualAA (d.hom ≫ d.inv) := by
        symm
        exact dualAbelianSchemeMapFromEvaluation_comp hA geometryA preservation MA evaluationA
          stability composition unitCoherence associativity comparison symmetry
          hB geometryB MB evaluationB hA geometryA MA evaluationA d.hom d.inv
      _ = dualAA (d.multiple • 𝟙 A) := congrArg dualAA d.hom_inv
      _ = d.multiple • 𝟙 DA := by
        rw [map_zsmul, dualAbelianSchemeMapAddHom_apply,
          dualAbelianSchemeMapFromEvaluation_id]
  inv_hom := by
    calc
      dualAB d.hom ≫ dualBA d.inv = dualBB (d.inv ≫ d.hom) := by
        symm
        exact dualAbelianSchemeMapFromEvaluation_comp hB geometryB preservation MB evaluationB
          stability composition unitCoherence associativity comparison symmetry
          hA geometryA MA evaluationA hB geometryB MB evaluationB d.inv d.hom
      _ = dualBB (d.multiple • 𝟙 B) := congrArg dualBB d.inv_hom
      _ = d.multiple • 𝟙 DB := by
        rw [map_zsmul, dualAbelianSchemeMapAddHom_apply,
          dualAbelianSchemeMapFromEvaluation_id]

include additivityAA additivityBB in
/-- The actual dual maps of both integral factors are finite etale isogenies
when the common positive multiplier is invertible on the base. -/
theorem dualIntegralInverseData_finiteEtaleIsogenies
    (d : Rationalization.IntegralInverseData A B) (hpos : 0 < d.multiple)
    (hn : IsUnit (d.multiple : Γ(S, ⊤))) :
    IsIsogeny (dualBA d.inv) ∧ Etale (hom (dualBA d.inv)) ∧
      IsIsogeny (dualAB d.hom) ∧ Etale (hom (dualAB d.hom)) :=
  integralInverseData_finiteEtaleIsogenies
    (dualIntegralInverseData preservation composition unitCoherence associativity comparison
      symmetry stability hA hB geometryA geometryB MA evaluationA MB evaluationB
      additivityAA additivityBB d) hpos hn

end Langlands.AbelianScheme

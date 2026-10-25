import Langlands.AlgebraicGeometry.Picard.DualMapAdditive
import Langlands.AbelianScheme.MultiplicationSpecialization
import Langlands.AbelianScheme.Torsion

/-! # Integer multiplication and torsion on the actual conditional dual -/

universe u

open CategoryTheory AlgebraicGeometry Limits
open scoped CategoryTheory.MonObj

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
variable (composition : PullbackTensorCompositionStatement.{u})
variable (unitCoherence : PullbackTensorUnitCoherenceStatement.{u})
variable (associativity : ExplicitPullbackTensorAssociativityStatement.{u})
variable (comparison : TensorMonoidalLeftUnitorComparisonStatement.{u})
variable (symmetry : PullbackTensorSymmetryStatement.{u})
variable (stability : PicardZeroPullbackStatement.{u})
variable {S : Scheme.{u}} {A B : AbelianScheme S}
variable (hA : HasDualScheme A) (hB : HasDualScheme B)
variable (additivity : DualSchemeMapAdditivity preservation stability A B hA hB)
variable (additivityAA : DualSchemeMapAdditivity preservation stability A A hA hA)
variable (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
variable (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
  structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
variable (MB : LineBundle ((relativeSpace B.X.hom).obj (dualScheme B hB)))
variable (evaluationB : tensorObj (poincareFamily B hB).obj.carrier MB.obj ≅
  structureSheaf ((relativeSpace B.X.hom).obj (dualScheme B hB)))

local notation "GA" => dualCommGroupSchemeFromEvaluation A hA preservation MA evaluationA
  stability composition unitCoherence associativity comparison symmetry

include additivity in
/-- The actual dual pullback map commutes with integer scaling of its input. -/
lemma dualGroupSchemeMap_zsmul (n : ℤ) (f : A ⟶ B) :
    dualCommGroupSchemeMapFromEvaluation preservation composition unitCoherence associativity
      comparison symmetry stability hA hB MA evaluationA MB evaluationB (n • f) =
    n • dualCommGroupSchemeMapFromEvaluation preservation composition unitCoherence associativity
      comparison symmetry stability hA hB MA evaluationA MB evaluationB f :=
  (dualGroupSchemeMapAddHom preservation composition unitCoherence associativity comparison
    symmetry stability hA hB additivity MA evaluationA MB evaluationB).map_zsmul n f


include additivityAA

/-- Dualizing integer multiplication gives integer multiplication on the dual group scheme. -/
lemma dualGroupSchemeMap_multiplication (n : ℤ) :
    dualCommGroupSchemeMapFromEvaluation preservation composition unitCoherence associativity
      comparison symmetry stability hA hA MA evaluationA MA evaluationA (multiplication A n) =
      n • 𝟙 GA := by
  rw [multiplication, dualGroupSchemeMap_zsmul preservation composition unitCoherence
    associativity comparison symmetry stability hA hA additivityAA,
    dualCommGroupSchemeMapFromEvaluation_id]

local notation "dn" n:arg => Langlands.CommGroupScheme.groupHom
  (dualCommGroupSchemeMapFromEvaluation preservation composition unitCoherence associativity
    comparison symmetry stability hA hA MA evaluationA MA evaluationA (multiplication A n))

/-- The preceding equality in the category of actual group objects. -/
lemma dualGroupSchemeMap_multiplication_groupHom (n : ℤ) :
    dn n = GroupScheme.multiplication (GA).toGrp n :=
  congrArg Langlands.CommGroupScheme.groupHom
    (dualGroupSchemeMap_multiplication preservation composition unitCoherence associativity
      comparison symmetry stability hA additivityAA MA evaluationA n)

/-- The dual map of `[n]` has the actual dual `n`-torsion scheme as its kernel. -/
def dualMultiplicationKernelIso (n : ℤ) :
    GroupScheme.kernel (dn n) ≅ GroupScheme.torsion (GA).toGrp n :=
  pullback.congrHom
    (dualGroupSchemeMap_multiplication_groupHom preservation composition unitCoherence
      associativity comparison symmetry stability hA additivityAA MA evaluationA n) rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma dualMultiplicationKernelIso_hom_ι (n : ℤ) :
    (dualMultiplicationKernelIso preservation composition unitCoherence associativity comparison
      symmetry stability hA additivityAA MA evaluationA n).hom ≫
        GroupScheme.torsionι (GA).toGrp n = GroupScheme.kernelι (dn n) := by
  simp [dualMultiplicationKernelIso, GroupScheme.torsionι, GroupScheme.kernelι,
    pullback.congrHom_hom, pullback.map]

@[reassoc (attr := simp)]
lemma dualMultiplicationKernelIso_inv_ι (n : ℤ) :
    (dualMultiplicationKernelIso preservation composition unitCoherence associativity comparison
      symmetry stability hA additivityAA MA evaluationA n).inv ≫
        GroupScheme.kernelι (dn n) = GroupScheme.torsionι (GA).toGrp n := by
  rw [← dualMultiplicationKernelIso_hom_ι preservation composition unitCoherence associativity
    comparison symmetry stability hA additivityAA MA evaluationA n, Iso.inv_hom_id_assoc]

variable (geometryA : DualSchemeGeometry A hA)

/-- With the existing explicit geometry proof, the same law holds for dual abelian schemes. -/
lemma dualAbelianSchemeMap_multiplication (n : ℤ) :
    dualAbelianSchemeMapFromEvaluation hA geometryA preservation MA evaluationA stability
      composition unitCoherence associativity comparison symmetry
      hA geometryA MA evaluationA (multiplication A n) =
    multiplication (dualAbelianSchemeFromEvaluation A hA geometryA preservation MA evaluationA
      stability composition unitCoherence associativity comparison symmetry) n :=
  dualGroupSchemeMap_multiplication preservation composition unitCoherence associativity
    comparison symmetry stability hA additivityAA MA evaluationA n

end Langlands.AbelianScheme

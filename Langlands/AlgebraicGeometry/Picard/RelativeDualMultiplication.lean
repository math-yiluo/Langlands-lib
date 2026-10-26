import Langlands.AlgebraicGeometry.Picard.DualMultiplication
import Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeMapAdditivityProof

/-! # Relative additive dualization, multiplication and torsion -/

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
variable {S : Scheme.{u}} [hS : QuasiSeparatedSpace S] {A B : AbelianScheme S}
variable (hA : HasDualScheme A) (hB : HasDualScheme B)
variable (MA : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
variable (evaluationA : tensorObj (poincareFamily A hA).obj.carrier MA.obj ≅
  structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hA)))
variable (MB : LineBundle ((relativeSpace B.X.hom).obj (dualScheme B hB)))
variable (evaluationB : tensorObj (poincareFamily B hB).obj.carrier MB.obj ≅
  structureSheaf ((relativeSpace B.X.hom).obj (dualScheme B hB)))

local notation "GA" => dualCommGroupSchemeFromEvaluation A hA preservation MA evaluationA
  stability composition unitCoherence associativity comparison symmetry
local notation "GB" => dualCommGroupSchemeFromEvaluation B hB preservation MB evaluationB
  stability composition unitCoherence associativity comparison symmetry
local notation "addAB" => relativeDualSchemeMapAdditivity preservation stability S A B hA hB
local notation "addAA" => relativeDualSchemeMapAdditivity preservation stability S A A hA hA

include hS

/-- Actual dual pullback maps bundled additively using proved relative additivity. -/
def relativeDualGroupSchemeMapAddHom : (A ⟶ B) →+ (GB ⟶ GA) :=
  dualGroupSchemeMapAddHom preservation composition unitCoherence associativity comparison
    symmetry stability hA hB addAB MA evaluationA MB evaluationB

@[simp] lemma relativeDualGroupSchemeMapAddHom_apply (f : A ⟶ B) :
    relativeDualGroupSchemeMapAddHom preservation composition unitCoherence associativity
      comparison symmetry stability hA hB MA evaluationA MB evaluationB f =
    dualCommGroupSchemeMapFromEvaluation preservation composition unitCoherence associativity
      comparison symmetry stability hA hB MA evaluationA MB evaluationB f := rfl

/-- Relative dualization preserves addition of input homomorphisms. -/
lemma relativeDualGroupSchemeMap_add (f g : A ⟶ B) :
    dualCommGroupSchemeMapFromEvaluation preservation composition unitCoherence associativity
      comparison symmetry stability hA hB MA evaluationA MB evaluationB (f + g) =
    dualCommGroupSchemeMapFromEvaluation preservation composition unitCoherence associativity
      comparison symmetry stability hA hB MA evaluationA MB evaluationB f +
    dualCommGroupSchemeMapFromEvaluation preservation composition unitCoherence associativity
      comparison symmetry stability hA hB MA evaluationA MB evaluationB g :=
  dualGroupSchemeMap_add preservation composition unitCoherence associativity comparison
    symmetry stability hA hB addAB MA evaluationA MB evaluationB f g

/-- Relative dualization commutes with every integer scalar. -/
lemma relativeDualGroupSchemeMap_zsmul (n : ℤ) (f : A ⟶ B) :
    dualCommGroupSchemeMapFromEvaluation preservation composition unitCoherence associativity
      comparison symmetry stability hA hB MA evaluationA MB evaluationB (n • f) =
    n • dualCommGroupSchemeMapFromEvaluation preservation composition unitCoherence associativity
      comparison symmetry stability hA hB MA evaluationA MB evaluationB f :=
  dualGroupSchemeMap_zsmul preservation composition unitCoherence associativity comparison
    symmetry stability hA hB addAB MA evaluationA MB evaluationB n f

/-- The actual relative dual of integer multiplication is integer multiplication. -/
lemma relativeDualGroupSchemeMap_multiplication (n : ℤ) :
    dualCommGroupSchemeMapFromEvaluation preservation composition unitCoherence associativity
      comparison symmetry stability hA hA MA evaluationA MA evaluationA (multiplication A n) =
      n • 𝟙 GA :=
  dualGroupSchemeMap_multiplication preservation composition unitCoherence associativity
    comparison symmetry stability hA addAA MA evaluationA n

local notation "dn" n:arg => Langlands.CommGroupScheme.groupHom
  (dualCommGroupSchemeMapFromEvaluation preservation composition unitCoherence associativity
    comparison symmetry stability hA hA MA evaluationA MA evaluationA (multiplication A n))

/-- The relative multiplication equation as equality of actual group-object maps. -/
lemma relativeDualGroupSchemeMap_multiplication_groupHom (n : ℤ) :
    dn n = GroupScheme.multiplication (GA).toGrp n :=
  dualGroupSchemeMap_multiplication_groupHom preservation composition unitCoherence
    associativity comparison symmetry stability hA addAA MA evaluationA n

/-- The actual dual multiplication kernel is the actual torsion scheme of the dual. -/
def relativeDualMultiplicationKernelIso (n : ℤ) :
    GroupScheme.kernel (dn n) ≅ GroupScheme.torsion (GA).toGrp n :=
  dualMultiplicationKernelIso preservation composition unitCoherence associativity comparison
    symmetry stability hA addAA MA evaluationA n

@[reassoc (attr := simp)]
lemma relativeDualMultiplicationKernelIso_hom_ι (n : ℤ) :
    (relativeDualMultiplicationKernelIso preservation composition unitCoherence associativity
      comparison symmetry stability hA MA evaluationA n).hom ≫
        GroupScheme.torsionι (GA).toGrp n = GroupScheme.kernelι (dn n) :=
  dualMultiplicationKernelIso_hom_ι preservation composition unitCoherence associativity
    comparison symmetry stability hA addAA MA evaluationA n

@[reassoc (attr := simp)]
lemma relativeDualMultiplicationKernelIso_inv_ι (n : ℤ) :
    (relativeDualMultiplicationKernelIso preservation composition unitCoherence associativity
      comparison symmetry stability hA MA evaluationA n).inv ≫
        GroupScheme.kernelι (dn n) = GroupScheme.torsionι (GA).toGrp n :=
  dualMultiplicationKernelIso_inv_ι preservation composition unitCoherence associativity
    comparison symmetry stability hA addAA MA evaluationA n

variable (geometryA : DualSchemeGeometry A hA) (geometryB : DualSchemeGeometry B hB)

local notation "FA" => dualAbelianSchemeFromEvaluation A hA geometryA preservation MA
  evaluationA stability composition unitCoherence associativity comparison symmetry
local notation "FB" => dualAbelianSchemeFromEvaluation B hB geometryB preservation MB
  evaluationB stability composition unitCoherence associativity comparison symmetry

/-- Relative additive dualization with explicit geometry witnesses at both endpoints. -/
def relativeDualAbelianSchemeMapAddHom : (A ⟶ B) →+ (FB ⟶ FA) :=
  dualAbelianSchemeMapAddHom preservation composition unitCoherence associativity comparison
    symmetry stability hA hB addAB MA evaluationA MB evaluationB geometryA geometryB

@[simp] lemma relativeDualAbelianSchemeMapAddHom_apply (f : A ⟶ B) :
    relativeDualAbelianSchemeMapAddHom preservation composition unitCoherence associativity
      comparison symmetry stability hA hB MA evaluationA MB evaluationB geometryA geometryB f =
    dualAbelianSchemeMapFromEvaluation hA geometryA preservation MA evaluationA stability
      composition unitCoherence associativity comparison symmetry hB geometryB MB evaluationB f :=
  rfl

/-- The same integer multiplication law on the constructed relative dual abelian scheme. -/
lemma relativeDualAbelianSchemeMap_multiplication (n : ℤ) :
    dualAbelianSchemeMapFromEvaluation hA geometryA preservation MA evaluationA stability
      composition unitCoherence associativity comparison symmetry
      hA geometryA MA evaluationA (multiplication A n) =
    multiplication FA n :=
  dualAbelianSchemeMap_multiplication preservation composition unitCoherence associativity
    comparison symmetry stability hA addAA MA evaluationA geometryA n

end Langlands.AbelianScheme

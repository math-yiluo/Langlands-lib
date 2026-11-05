import Langlands.GroupScheme.Descent.TensorFullCoverStatement
import Langlands.GroupScheme.Descent.TensorCoverDescent
import Langlands.GroupScheme.Descent.TensorFiniteness
import Langlands.GroupScheme.SimplyConnected.CoverComparison
import Langlands.GroupScheme.SimplyConnected.AlgebraicExtensionReflection
import Langlands.GroupScheme.SimplyConnected.FieldComponentUniversalReflection
import Langlands.GroupScheme.Reductive.SemisimpleFieldReflectionProof

/-! # Full simply connected cover descent from an explicit finite tensor decomposition -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.GroupScheme

open Descent

/-- A simply connected cover of `G_L` descends to a simply connected cover of `G`
when `L ⊗[k] L` has an explicit finite decomposition by automorphisms of `L/k`. -/
theorem simplyConnectedCoverTensorDescent :
    SimplyConnectedCoverTensorDescentStatement.{u,v} := by
  intro k L _ _ _ J _ e s he G C π hπ
  have : Algebra.IsAlgebraic k L := isAlgebraic_of_tensorDecomposition e
  let S := hπ.tensorDescentSolution e s he
  let a := hπ.tensorDescentCentralIsogeny e s he
  have hrec : (baseChange (fieldMap k L)).map a.val = S.iso.hom ≫ π :=
    hπ.baseChange_tensorDescentCentralIsogeny e s he
  refine ⟨S.obj, a.val, S.iso,
    ⟨IsSemisimple.of_fieldExtension hπ.isSemisimple,
      simplyConnectedAlgebraicExtensionReflection k L S.obj
        (hπ.isSimplyConnected.of_iso S.iso),
      a.property, ?_⟩, hrec⟩
  refine centralCoverUniversalPropertyTensorReflection k L S.obj G a.val
    (Fin (Fintype.card J)) (finiteTensorEquiv e)
    (fun i => s ((Fintype.equivFin J).symm i))
    (fun x y i => by simpa using he x y ((Fintype.equivFin J).symm i)) ?_
  rw [hrec]
  exact hπ.universal.iso_comp S.iso

end Langlands.GroupScheme

import Langlands.Representation.Plancherel.RationalContinuousFixedBasesStatement
import Langlands.Representation.Plancherel.UnramifiedRationalFixedMatrices
import Langlands.Representation.Plancherel.UnramifiedRationalNormalizedInducedFinitenessProof
import Langlands.Representation.Plancherel.RationalNormalizedInducedSpecializationProof
import Mathlib.LinearAlgebra.Dimension.Free

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal TensorProduct
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel.RationalNormalized

attribute [local instance] matrixInducedAddCommGroup matrixInducedModule
  matrixInducedSMul matrixInducedMulAction matrixInducedComplexModule
  matrixInducedComplexSMul matrixInducedScalarTower matrixInducedSMulCommClass
  matrixInducedCompatible matrixFixedModule

set_option maxHeartbeats 800000 in
/-- Universal finite freeness and actual specialization supply all fiber bases. -/
theorem rationalContinuousFixedBases.{u,uV} :
    RationalContinuousFixedBasesStatement.{u,uV} := by
  intro F _ _ _ _ G hG
  let := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  intro _ _ _ _ A M P U _ p l a r n h hU hr hQ π hπ K hK mHaar _
  let : CompactSpace (Induction.LeftQuotient (ParabolicPoints p)) := hQ
  have hP : IsClosed (ParabolicPoints p : Set (rationalPoints G)) := by
    let : T2Space F := Langlands.BruhatTits.localField_t2Space F
    have hp : IsClosedSubgroup p := r.isCompatible.parabolic.isClosedSubgroup
    have : IsClosedImmersion p.hom.hom.left := hp
    have hrep : (SubgroupFunctor.range p).IsRepresentedBy p :=
      ⟨Over.mono_of_mono_left _, rfl⟩
    exact isClosed_rationalPoint_subgroup F (SubgroupFunctor.range p) p hrep hp
  have hf := universalInduced_fixed_finite_free (parabolicLeviRationalNormCharacters r)
    (continuous_parabolicLeviRationalNormCharacters r) h hU hr π hπ hP K hK
  let : Module (RegularAlgebra r)
      (fixedVectors (inducedRepresentation r h hU π.representation) K.toSubgroup) :=
    Submodule.module _
  let : Module.Finite (RegularAlgebra r)
      (fixedVectors (inducedRepresentation r h hU π.representation) K.toSubgroup) := hf.1
  let : Module.Free (RegularAlgebra r)
      (fixedVectors (inducedRepresentation r h hU π.representation) K.toSubgroup) := hf.2
  let er := Langlands.Jacquet.CoefficientRestriction.complexFixedVectorsEquiv
    (inducedRepresentation r h hU π.representation) K.toSubgroup
  let : Module.Finite (RegularAlgebra r)
      (fixedVectors (inducedComplexRepresentation r h hU π) K.toSubgroup) :=
    Module.Finite.equiv er.symm
  let : Module.Free (RegularAlgebra r)
      (fixedVectors (inducedComplexRepresentation r h hU π) K.toSubgroup) :=
    Module.Free.of_equiv er.symm
  let e := Module.finBasis (RegularAlgebra r)
    (fixedVectors (inducedComplexRepresentation r h hU π) K.toSubgroup)
  have hbij : ∀ χ, InducedSpecializationBijective r h hU π χ :=
    fun χ => rationalNormalizedInducedSpecialization F G hG M P U A p l a r n h hU
      hr hQ π χ
  exact ⟨_, fun χ => inducedSpecializedBasis r h hU π K hK e χ (hbij χ),
    inducedSpecializedBasis_continuous r h hU π K hK e mHaar hbij⟩

end Langlands.Plancherel.RationalNormalized

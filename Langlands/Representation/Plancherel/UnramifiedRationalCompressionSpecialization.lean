import Langlands.Representation.Plancherel.RationalNormalizedInducedSpecializationStatement
import Langlands.Representation.Jacquet.CoefficientScalarRestriction

/-! Actual rational normalized induction and compact compression specialization. -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal TensorProduct
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel.RationalNormalized

universe u uV

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G M P U : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine M.X.left]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation p l a)

local instance compressionAmbientAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance compressionPointTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X

local instance compressionTensorAddCommGroup (E : Type*) [AddCommGroup E] [Module ℂ E] :
    AddCommGroup (RegularAlgebra r ⊗[ℂ] E) := TensorProduct.addCommGroup

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {n : U ⟶ P}
  (h : Aubert.General.IsSemidirectDecomposition (ParabolicPoints p)
    (parabolicLeviPointSubgroup p l) (UnipotentPoints (p := p) n))
  (hU : IsClosed (UnipotentPoints (p := p) n : Set (rationalPoints G)))

local instance compressionInducedAddCommGroup
    (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l)) :
    AddCommGroup (Induced r h hU π.representation) :=
  Induction.smoothFunctionsAddCommGroup _ (inducingRepresentation r h hU π.representation)

local instance compressionInducedModule
    (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l)) :
    Module (RegularAlgebra r) (Induced r h hU π.representation) := Submodule.module _

local instance compressionInducedSMul
    (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l)) :
    SMul (RegularAlgebra r) (Induced r h hU π.representation) :=
  (compressionInducedModule r h hU π).toSMul

local instance compressionInducedMulAction
    (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l)) :
    MulAction (RegularAlgebra r) (Induced r h hU π.representation) :=
  (compressionInducedModule r h hU π).toMulAction

local instance compressionInducedComplexModule
    (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l)) :
    Module ℂ (Induced r h hU π.representation) :=
  Module.compHom _ (algebraMap ℂ (RegularAlgebra r))

local instance compressionInducedComplexSMul
    (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l)) :
    SMul ℂ (Induced r h hU π.representation) :=
  (compressionInducedComplexModule r h hU π).toSMul

local instance compressionInducedScalarTower
    (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l)) :
    IsScalarTower ℂ (RegularAlgebra r) (Induced r h hU π.representation) :=
  IsScalarTower.of_compHom ℂ (RegularAlgebra r) _

/-- The actual universal induced action, with only its scalars restricted. -/
def inducedComplexRepresentation
    (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l)) :
    Representation ℂ (rationalPoints G) (Induced r h hU π.representation) :=
  @Langlands.Jacquet.CoefficientRestriction.complexRepresentation
    (RegularAlgebra r) _ _ (rationalPoints G) _ (Induced r h hU π.representation)
    (compressionInducedAddCommGroup r h hU π) (compressionInducedModule r h hU π)
    (compressionInducedComplexModule r h hU π) (compressionInducedScalarTower r h hU π)
    (inducedRepresentation r h hU π.representation)

/-- Scalar restriction retains the smoothness of the actual induced action. -/
theorem isSmooth_inducedComplexRepresentation
    (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l)) :
    IsSmooth (inducedComplexRepresentation r h hU π) :=
  isSmooth_inducedRepresentation r h hU π.representation

instance inducedComplexRepresentation_hasCompatibleCoefficients
    (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l)) :
    HasCompatibleCoefficients (RegularAlgebra r) (inducedComplexRepresentation r h hU π) where
  map_smul b g v := (inducedRepresentation r h hU π.representation g).map_smul b v

/-- Actual function-value evaluation as a complex intertwiner on the same carrier. -/
def inducedEvaluationIntertwiner
    (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l))
    (χ : unramifiedCharacters (parabolicLeviRationalNormCharacters r)) :
    (inducedComplexRepresentation r h hU π).IntertwiningMap
      (complexInduced r h hU π χ).representation where
  toLinearMap :=
    { toFun := inducedEvaluation r h hU π χ
      map_add' := map_add (inducedEvaluation r h hU π χ)
      map_smul' z v := by
        change inducedEvaluation r h hU π χ
          (algebraMap ℂ (RegularAlgebra r) z • v) = _
        exact (inducedEvaluation r h hU π χ).map_smulₛₗ
          (algebraMap ℂ (RegularAlgebra r) z) v }
  isIntertwining' g := by
    exact LinearMap.ext (fun v => inducedEvaluation_action r h hU π χ g v)

/-- The intertwiner retains evaluation of every actual regular coefficient. -/
theorem inducedEvaluationIntertwiner_regular_smul
    (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l))
    (χ : unramifiedCharacters (parabolicLeviRationalNormCharacters r))
    (b : RegularAlgebra r) (v : Induced r h hU π.representation) :
    inducedEvaluationIntertwiner r h hU π χ (b • v) =
      evaluation r χ b • inducedEvaluationIntertwiner r h hU π χ v :=
  (inducedEvaluation r h hU π χ).map_smulₛₗ b v

end Langlands.Plancherel.RationalNormalized

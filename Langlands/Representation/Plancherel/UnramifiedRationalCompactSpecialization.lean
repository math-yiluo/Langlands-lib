import Langlands.Representation.Plancherel.UnramifiedRationalCompressionSpecialization
import Langlands.Representation.Compact.CoefficientSpecialization

/-! Actual rational induced compact specialization and fixed compression powers. -/

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

local instance compactAmbientAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance compactPointTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X

local instance compactTensorAddCommGroup (E : Type*) [AddCommGroup E] [Module ℂ E] :
    AddCommGroup (RegularAlgebra r ⊗[ℂ] E) := TensorProduct.addCommGroup

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {n : U ⟶ P}
  (h : Aubert.General.IsSemidirectDecomposition (ParabolicPoints p)
    (parabolicLeviPointSubgroup p l) (UnipotentPoints (p := p) n))
  (hU : IsClosed (UnipotentPoints (p := p) n : Set (rationalPoints G)))

local instance compactInducedAddCommGroup
    (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l)) :
    AddCommGroup (Induced r h hU π.representation) :=
  compressionInducedAddCommGroup r h hU π

local instance compactInducedModule
    (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l)) :
    Module (RegularAlgebra r) (Induced r h hU π.representation) :=
  compressionInducedModule r h hU π

local instance compactInducedSMul
    (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l)) :
    SMul (RegularAlgebra r) (Induced r h hU π.representation) :=
  compressionInducedSMul r h hU π

local instance compactInducedMulAction
    (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l)) :
    MulAction (RegularAlgebra r) (Induced r h hU π.representation) :=
  compressionInducedMulAction r h hU π

local instance compactInducedComplexModule
    (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l)) :
    Module ℂ (Induced r h hU π.representation) :=
  compressionInducedComplexModule r h hU π

local instance compactInducedComplexSMul
    (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l)) :
    SMul ℂ (Induced r h hU π.representation) :=
  compressionInducedComplexSMul r h hU π

local instance compactInducedScalarTower
    (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l)) :
    IsScalarTower ℂ (RegularAlgebra r) (Induced r h hU π.representation) :=
  compressionInducedScalarTower r h hU π

local instance compactInducedSMulCommClass
    (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l)) :
    SMulCommClass ℂ (RegularAlgebra r) (Induced r h hU π.representation) where
  smul_comm z b v := by
    change algebraMap ℂ (RegularAlgebra r) z • (b • v) =
      b • (algebraMap ℂ (RegularAlgebra r) z • v)
    rw [smul_smul, smul_smul, mul_comm]

local instance compactInducedCompatible
    (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l)) :
    HasCompatibleCoefficients (RegularAlgebra r) (inducedComplexRepresentation r h hU π) :=
  inducedComplexRepresentation_hasCompatibleCoefficients r h hU π

local instance compactFixedModule
    (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l))
    (H : Subgroup (rationalPoints G)) :
    Module (RegularAlgebra r) (fixedVectors (inducedComplexRepresentation r h hU π) H) :=
  @coefficientFixedVectorsModule (RegularAlgebra r) _ (rationalPoints G) _
    (Induced r h hU π.representation) (compactInducedAddCommGroup r h hU π)
    (compactInducedComplexModule r h hU π) (compactInducedModule r h hU π)
    (inducedComplexRepresentation r h hU π) (compactInducedCompatible r h hU π) H

variable (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l))
  (χ : unramifiedCharacters (parabolicLeviRationalNormCharacters r))

/-- The generic scalar extension is the actual function-value scalar extension. -/
abbrev InducedGenericScalarExtensionEq : Prop :=
  letI : Algebra (RegularAlgebra r) ℂ := (evaluation r χ).toAlgebra
  Compact.CoefficientSpecialization.scalarExtension (RegularAlgebra r)
    (inducedComplexRepresentation r h hU π) (complexInduced r h hU π χ).representation
    (inducedEvaluationIntertwiner r h hU π χ)
    (inducedEvaluationIntertwiner_regular_smul r h hU π χ) =
      inducedScalarExtension r h hU π χ

theorem inducedGenericScalarExtension_eq : InducedGenericScalarExtensionEq r h hU π χ := by
  let : Algebra (RegularAlgebra r) ℂ := (evaluation r χ).toAlgebra
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul z v => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The canonical actual specialization of fixed vectors under any subgroup. -/
def inducedFixedScalarExtension (H : Subgroup (rationalPoints G)) :
    letI : Algebra (RegularAlgebra r) ℂ := (evaluation r χ).toAlgebra
    ℂ ⊗[RegularAlgebra r] fixedVectors (inducedComplexRepresentation r h hU π) H →ₗ[ℂ]
      fixedVectors (complexInduced r h hU π χ).representation H := by
  letI : Algebra (RegularAlgebra r) ℂ := (evaluation r χ).toAlgebra
  exact Compact.CoefficientSpecialization.fixedScalarExtension (RegularAlgebra r)
    (inducedComplexRepresentation r h hU π) (complexInduced r h hU π χ).representation
    (inducedEvaluationIntertwiner r h hU π χ)
    (inducedEvaluationIntertwiner_regular_smul r h hU π χ) H

variable (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))

/-- Full actual induced specialization supplies the compact-fixed equivalence. -/
def inducedFixedScalarExtensionEquiv
    (hbij : InducedSpecializationBijective r h hU π χ) :
    letI : Algebra (RegularAlgebra r) ℂ := (evaluation r χ).toAlgebra
    ℂ ⊗[RegularAlgebra r]
        fixedVectors (inducedComplexRepresentation r h hU π) K.toSubgroup ≃ₗ[ℂ]
      fixedVectors (complexInduced r h hU π χ).representation K.toSubgroup := by
  letI : Algebra (RegularAlgebra r) ℂ := (evaluation r χ).toAlgebra
  apply Compact.CoefficientSpecialization.fixedScalarExtensionEquiv (RegularAlgebra r)
    (inducedComplexRepresentation r h hU π) (complexInduced r h hU π χ).representation
    (inducedEvaluationIntertwiner r h hU π χ)
    (inducedEvaluationIntertwiner_regular_smul r h hU π χ)
    (isSmooth_inducedComplexRepresentation r h hU π) (complexInduced r h hU π χ).isSmooth K hK
  exact Eq.mpr (congrArg (fun T : InducedSpecializationFiber r h hU π χ →ₗ[ℂ]
      complexInduced r h hU π χ => Function.Bijective T)
    (inducedGenericScalarExtension_eq r h hU π χ)) hbij

/-- Stability of the supplied universal compression power transfers unchanged. -/
theorem inducedCompressedAction_stablePower
    (hbij : InducedSpecializationBijective r h hU π χ)
    (g : rationalPoints G) (b : ℕ)
    (hstable : LinearAlgebra.StableEndomorphism.Stable
      (Jacquet.compressedAction (inducedComplexRepresentation r h hU π)
        (isSmooth_inducedComplexRepresentation r h hU π) K hK g ^ b)) :
    LinearAlgebra.StableEndomorphism.Stable
      (Jacquet.compressedAction (complexInduced r h hU π χ).representation
        (complexInduced r h hU π χ).isSmooth K hK g ^ b) := by
  let : Algebra (RegularAlgebra r) ℂ := (evaluation r χ).toAlgebra
  apply Compact.CoefficientSpecialization.compressedAction_stablePower (RegularAlgebra r)
    (inducedComplexRepresentation r h hU π) (complexInduced r h hU π χ).representation
    (inducedEvaluationIntertwiner r h hU π χ)
    (inducedEvaluationIntertwiner_regular_smul r h hU π χ)
    (isSmooth_inducedComplexRepresentation r h hU π) (complexInduced r h hU π χ).isSmooth K hK
    _ g b hstable
  exact Eq.mpr (congrArg (fun T : InducedSpecializationFiber r h hU π χ →ₗ[ℂ]
      complexInduced r h hU π χ => Function.Bijective T)
    (inducedGenericScalarExtension_eq r h hU π χ)) hbij

end Langlands.Plancherel.RationalNormalized

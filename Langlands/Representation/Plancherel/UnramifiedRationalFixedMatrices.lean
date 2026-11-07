import Langlands.Representation.Compact.CoefficientFixedMatrices
import Langlands.Representation.Plancherel.UnramifiedRationalCompactSpecialization
import Langlands.Representation.Plancherel.RationalUnramifiedScalarCancellation

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal TensorProduct
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel.RationalNormalized

universe u uV un

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G M P U : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine M.X.left]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation p l a)

local instance matrixAmbientAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance matrixPointTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {n : U ⟶ P}
  (h : Aubert.General.IsSemidirectDecomposition (ParabolicPoints p)
    (parabolicLeviPointSubgroup p l) (UnipotentPoints (p := p) n))
  (hU : IsClosed (UnipotentPoints (p := p) n : Set (rationalPoints G)))

local instance matrixInducedAddCommGroup
    (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l)) :
    AddCommGroup (Induced r h hU π.representation) :=
  compactInducedAddCommGroup r h hU π

local instance matrixInducedModule
    (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l)) :
    Module (RegularAlgebra r) (Induced r h hU π.representation) :=
  compactInducedModule r h hU π

local instance matrixInducedSMul
    (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l)) :
    SMul (RegularAlgebra r) (Induced r h hU π.representation) :=
  compactInducedSMul r h hU π

local instance matrixInducedMulAction
    (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l)) :
    MulAction (RegularAlgebra r) (Induced r h hU π.representation) :=
  compactInducedMulAction r h hU π

local instance matrixInducedComplexModule
    (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l)) :
    Module ℂ (Induced r h hU π.representation) :=
  compactInducedComplexModule r h hU π

local instance matrixInducedComplexSMul
    (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l)) :
    SMul ℂ (Induced r h hU π.representation) :=
  compactInducedComplexSMul r h hU π

local instance matrixInducedScalarTower
    (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l)) :
    IsScalarTower ℂ (RegularAlgebra r) (Induced r h hU π.representation) :=
  compactInducedScalarTower r h hU π

local instance matrixInducedSMulCommClass
    (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l)) :
    SMulCommClass ℂ (RegularAlgebra r) (Induced r h hU π.representation) :=
  compactInducedSMulCommClass r h hU π

local instance matrixInducedCompatible
    (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l)) :
    HasCompatibleCoefficients (RegularAlgebra r) (inducedComplexRepresentation r h hU π) :=
  inducedComplexRepresentation_hasCompatibleCoefficients r h hU π

local instance matrixFixedModule
    (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l))
    (H : Subgroup (rationalPoints G)) :
    Module (RegularAlgebra r) (fixedVectors (inducedComplexRepresentation r h hU π) H) :=
  compactFixedModule r h hU π H

variable (π : SmoothRep.{0, u, uV} ℂ (parabolicLeviPointSubgroup p l))
  (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
  {idx : Type un}
  (e : Module.Basis idx (RegularAlgebra r)
    (fixedVectors (inducedComplexRepresentation r h hU π) K.toSubgroup))

/-- Evaluate a universal coefficient basis to obtain a basis of the actual fiber. -/
def inducedSpecializedBasis
    (χ : unramifiedCharacters (parabolicLeviRationalNormCharacters r))
    (hbij : InducedSpecializationBijective r h hU π χ) :
    Module.Basis idx ℂ
      (fixedVectors (complexInduced r h hU π χ).representation K.toSubgroup) := by
  letI : Algebra (RegularAlgebra r) ℂ := (evaluation r χ).toAlgebra
  apply Compact.CoefficientSpecialization.specializedBasis (RegularAlgebra r)
    (inducedComplexRepresentation r h hU π) (complexInduced r h hU π χ).representation
    (inducedEvaluationIntertwiner r h hU π χ)
    (inducedEvaluationIntertwiner_regular_smul r h hU π χ)
    (isSmooth_inducedComplexRepresentation r h hU π) (complexInduced r h hU π χ).isSmooth
    K hK _ e
  exact Eq.mpr (congrArg (fun T : InducedSpecializationFiber r h hU π χ →ₗ[ℂ]
      complexInduced r h hU π χ => Function.Bijective T)
    (inducedGenericScalarExtension_eq r h hU π χ)) hbij

variable [MeasurableSpace (rationalPoints G)] [BorelSpace (rationalPoints G)]
  (mHaar : Measure (rationalPoints G)) [mHaar.IsHaarMeasure] [Fintype idx]

/-- The actual fiber matrix entry is the evaluation of one fixed regular function. -/
abbrev InducedSpecializedBasisFixedMatrix
    (χ : unramifiedCharacters (parabolicLeviRationalNormCharacters r))
    (hbij : InducedSpecializationBijective r h hU π χ)
    (g : rationalPoints G) (i j : idx) : Prop :=
  UnitarizabilityContinuation.fixedMatrix mHaar (complexInduced r h hU π χ).isSmooth hK
    (inducedSpecializedBasis r h hU π K hK e χ hbij)
    (complexInduced r h hU π χ).representation g i j =
      (e.repr (Hecke.fixedProjection mHaar (inducedComplexRepresentation r h hU π)
        (isSmooth_inducedComplexRepresentation r h hU π) K hK
        (inducedComplexRepresentation r h hU π g (e j))) i).val χ

theorem inducedSpecializedBasis_fixedMatrix
    (χ : unramifiedCharacters (parabolicLeviRationalNormCharacters r))
    (hbij : InducedSpecializationBijective r h hU π χ)
    (g : rationalPoints G) (i j : idx) :
    InducedSpecializedBasisFixedMatrix r h hU π K hK e mHaar χ hbij g i j := by
  let : Algebra (RegularAlgebra r) ℂ := (evaluation r χ).toAlgebra
  exact Compact.CoefficientSpecialization.specializedBasis_fixedMatrix (RegularAlgebra r)
    (inducedComplexRepresentation r h hU π) (complexInduced r h hU π χ).representation
    (inducedEvaluationIntertwiner r h hU π χ)
    (inducedEvaluationIntertwiner_regular_smul r h hU π χ)
    (isSmooth_inducedComplexRepresentation r h hU π) (complexInduced r h hU π χ).isSmooth
    K hK _ e mHaar g i j

/-- Continuity for the full complex unramified character topology. -/
abbrev InducedSpecializedBasisContinuous
    (hbij : ∀ χ, InducedSpecializationBijective r h hU π χ) : Prop :=
  ∀ (g : rationalPoints G) (i j : idx),
    Continuous (fun χ => UnitarizabilityContinuation.fixedMatrix mHaar
      (complexInduced r h hU π χ).isSmooth hK
      (inducedSpecializedBasis r h hU π K hK e χ (hbij χ))
      (complexInduced r h hU π χ).representation g i j)

theorem inducedSpecializedBasis_continuous
    (hbij : ∀ χ, InducedSpecializationBijective r h hU π χ) :
    InducedSpecializedBasisContinuous r h hU π K hK e mHaar hbij := by
  intro g i j
  have he : (fun χ => UnitarizabilityContinuation.fixedMatrix mHaar
      (complexInduced r h hU π χ).isSmooth hK
      (inducedSpecializedBasis r h hU π K hK e χ (hbij χ))
      (complexInduced r h hU π χ).representation g i j) =
      (e.repr (Hecke.fixedProjection mHaar (inducedComplexRepresentation r h hU π)
        (isSmooth_inducedComplexRepresentation r h hU π) K hK
        (inducedComplexRepresentation r h hU π g (e j))) i).val := by
    funext χ
    exact inducedSpecializedBasis_fixedMatrix r h hU π K hK e mHaar χ (hbij χ) g i j
  rw [he]
  exact continuous_unramifiedRegularFunction _ _

end Langlands.Plancherel.RationalNormalized

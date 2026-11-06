import Langlands.Representation.Induction.Definitions
import Langlands.Representation.CuspidalSupport.RationalInertia
import Langlands.Representation.Category.RestrictionSubquotients
import Langlands.Representation.Category.UniverseLiftFunctor
import Langlands.Representation.Plancherel.RationalUnramifiedCoordinateAlgebra
import Langlands.Representation.Plancherel.UnramifiedUniversalTwist

/-! Actual compact induction and universal tensor in Renard VI.4.1. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.CuspidalSupport

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local instance : TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X

local instance : IsTopologicalGroup (GroupScheme.rationalPoints G) :=
  rationalPoint_isTopologicalGroup F G

/-- Actual covariant functions, smooth under right translation and compactly
supported modulo the common kernel of every rational-character norm. -/
abbrev RationalNormKernelCompactFunctions
    (π : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G)) :
    Type (max uF uV) :=
  Induction.CompactFunctions (rationalCommonNormKernel G)
    (π.representation.comp (rationalCommonNormKernel G).subtype)

/-- The action is literally the existing compact induction of the entire restriction. -/
abbrev rationalNormKernelCompactRepresentation
    (π : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G)) :
    Representation ℂ (GroupScheme.rationalPoints G)
      (RationalNormKernelCompactFunctions G π) :=
  Induction.compactInduced (rationalCommonNormKernel G)
    (π.representation.comp (rationalCommonNormKernel G).subtype)

/-- Renard's alternative candidate Π₁, defined for every smooth π. -/
def rationalNormKernelCompactInduction
    (π : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G)) :
    SmoothRep.{0, uF, max uF uV} ℂ (GroupScheme.rationalPoints G) :=
  SmoothRep.of (rationalNormKernelCompactRepresentation G π)
    (Induction.compactInduced_smooth _ _)

/-- Evaluation of an actual compactly induced function. -/
def rationalNormKernelCompactEval
    (π : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G))
    (f : RationalNormKernelCompactFunctions G π) (x : GroupScheme.rationalPoints G) : π :=
  Induction.eval _ _ f.val x

/-- The defining covariance uses the original restricted action. -/
theorem rationalNormKernelCompactEval_covariant
    (π : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G))
    (f : RationalNormKernelCompactFunctions G π)
    (k : rationalCommonNormKernel G) (x : GroupScheme.rationalPoints G) :
    rationalNormKernelCompactEval G π f ((k : GroupScheme.rationalPoints G) * x) =
      π.representation (k : GroupScheme.rationalPoints G)
        (rationalNormKernelCompactEval G π f x) :=
  f.val.val.property k x

/-- The actual projected nonzero support is compact, rather than a supplied support bound. -/
theorem rationalNormKernelCompactEval_compactSupport
    (π : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G))
    (f : RationalNormKernelCompactFunctions G π) :
    IsCompact (Induction.quotientSupport (rationalCommonNormKernel G)
      (rationalNormKernelCompactEval G π f)) :=
  f.property

/-- The compactly induced action is right translation. -/
theorem rationalNormKernelCompactEval_action
    (π : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G))
    (f : RationalNormKernelCompactFunctions G π) (g x : GroupScheme.rationalPoints G) :
    rationalNormKernelCompactEval G π (rationalNormKernelCompactRepresentation G π g f) x =
      rationalNormKernelCompactEval G π f (x * g) := rfl

/-- Restriction and compact induction act functorially by postcomposition. -/
def rationalNormKernelCompactInductionFunctor :
    SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (GroupScheme.rationalPoints G) :=
  SmoothRep.restrictSubgroupFunctor (rationalCommonNormKernel G) ⋙
    SmoothRep.toRep ⋙ Induction.compactInductionFunctor (rationalCommonNormKernel G)

@[simp]
theorem rationalNormKernelCompactInductionFunctor_obj
    (π : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G)) :
    (rationalNormKernelCompactInductionFunctor G).obj π =
      rationalNormKernelCompactInduction G π := rfl

/-- The concrete evaluation-generated algebra B for the complete rational norm family. -/
abbrev rationalUnramifiedRegularAlgebra :=
  unramifiedRegularFunctions (fun χ => (rationalNormCharacters G χ).toMul)

/-- The published actual universal tensor carrier, with its universe displayed. -/
abbrev RationalUniversalTensor
    (π : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G)) :
    Type (max uF uV) :=
  rationalUnramifiedRegularAlgebra G ⊗[ℂ] π

local instance tensorAddCommGroup
    (π : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G)) :
    AddCommGroup (RationalUniversalTensor G π) := TensorProduct.addCommGroup

/-- Restrict the published B-linear universal action to complex scalars, retaining
its actual operators and its full norm family. -/
def rationalUniversalTensorRepresentation
    (π : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G)) :
    Representation ℂ (GroupScheme.rationalPoints G) (RationalUniversalTensor G π) where
  toFun g :=
    (universalUnramifiedRepresentation
      (fun χ => (rationalNormCharacters G χ).toMul) π.representation g).restrictScalars ℂ
  map_one' := by
    apply LinearMap.ext
    intro t
    exact congrArg (fun T => T t) (map_one
      (universalUnramifiedRepresentation
        (fun χ => (rationalNormCharacters G χ).toMul) π.representation))
  map_mul' g h := by
    apply LinearMap.ext
    intro t
    exact congrArg (fun T => T t) (map_mul
      (universalUnramifiedRepresentation
        (fun χ => (rationalNormCharacters G χ).toMul) π.representation) g h)

omit [LocallyOfFiniteType G.X.hom] in
/-- The universal action multiplies by b_g(χ)=χ(g) and acts by π(g). -/
theorem rationalUniversalTensorRepresentation_tmul
    (π : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G))
    (g : GroupScheme.rationalPoints G) (b : rationalUnramifiedRegularAlgebra G) (v : π) :
    rationalUniversalTensorRepresentation G π g (b ⊗ₜ[ℂ] v) =
      (unramifiedEvaluationRegular (fun χ => (rationalNormCharacters G χ).toMul) g * b)
        ⊗ₜ[ℂ] (π.representation g v) := rfl

/-- Smoothness follows from the already proved openness of the full common kernel. -/
theorem rationalUniversalTensorRepresentation_smooth
    (π : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G)) :
    IsSmooth (rationalUniversalTensorRepresentation G π) :=
  isSmooth_universalUnramifiedRepresentation
    (fun χ => (rationalNormCharacters G χ).toMul) π.representation π.isSmooth
    (isOpen_rationalCommonNormKernel G)

/-- The actual universal unramified tensor as a complex smooth representation. -/
def rationalUniversalTensorSmoothRep
    (π : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G)) :
    SmoothRep.{0, uF, max uF uV} ℂ (GroupScheme.rationalPoints G) :=
  SmoothRep.of (rationalUniversalTensorRepresentation G π)
    (rationalUniversalTensorRepresentation_smooth G π)

/-- The base of the inertia block at the function-carrier universe; the action
is transported along the published, functorial `ULift` construction. -/
abbrev rationalInertiaBaseLift
    (π : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G)) :
    SmoothRep.{0, uF, max uF uV} ℂ (GroupScheme.rationalPoints G) :=
  (SmoothRep.universeLiftFunctor.{uF, uF, uV} (GroupScheme.rationalPoints G)).obj π

end Langlands.CuspidalSupport

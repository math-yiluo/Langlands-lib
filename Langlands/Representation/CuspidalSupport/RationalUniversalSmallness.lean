import Langlands.Representation.CuspidalSupport.RationalUniversalSmallProgeneratorStatement
import Langlands.Representation.CuspidalSupport.RationalInertiaCoproducts
import Langlands.Representation.Induction.OpenFiniteGeneration
import Langlands.Representation.Category.FiniteGenerationCoproducts

/-! # Finite generation and smallness of the actual norm-kernel induction -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open Langlands.CategoryTheory.Renard
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local instance rationalUniversalSmallnessTopology :
    TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X

local instance rationalUniversalSmallnessTopologicalGroup :
    IsTopologicalGroup (GroupScheme.rationalPoints G) :=
  rationalPoint_isTopologicalGroup F G

variable (π : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G))

/-- Finite generation of the entire actual restriction implies finite
generation of its actual compact induction. -/
theorem finite_rationalNormKernelCompactInduction_of_finite_restriction
    [Module.Finite (MonoidAlgebra ℂ (rationalCommonNormKernel G))
      (SmoothRep.restrictSubgroup (rationalCommonNormKernel G) π).representation.asModule] :
    Module.Finite (MonoidAlgebra ℂ (GroupScheme.rationalPoints G))
      (rationalNormKernelCompactInduction G π).representation.asModule :=
  Induction.finite_compactInduced_of_finite (rationalCommonNormKernel G)
    (isOpen_rationalCommonNormKernel G)
    (SmoothRep.restrictSubgroup (rationalCommonNormKernel G) π)

/-- Finite composition length of the actual restriction supplies the finite
generation needed for compact induction. -/
theorem finite_rationalNormKernelCompactInduction_of_finiteLength
    (hfinite : IsFiniteLength (MonoidAlgebra ℂ (rationalCommonNormKernel G))
      (SmoothRep.restrictSubgroup (rationalCommonNormKernel G) π).representation.asModule) :
    Module.Finite (MonoidAlgebra ℂ (GroupScheme.rationalPoints G))
      (rationalNormKernelCompactInduction G π).representation.asModule := by
  let := (isFiniteLength_iff_isNoetherian_isArtinian.mp hfinite).1
  exact finite_rationalNormKernelCompactInduction_of_finite_restriction G π

/-- A chosen finite spanning set for the group-algebra module of the actual
full-restriction compact induction. -/
def rationalNormKernelCompactFiniteGenerators
    (hfinite : IsFiniteLength (MonoidAlgebra ℂ (rationalCommonNormKernel G))
      (SmoothRep.restrictSubgroup (rationalCommonNormKernel G) π).representation.asModule) :
    {s : Finset (rationalNormKernelCompactInduction G π).representation.asModule //
      Submodule.span (MonoidAlgebra ℂ (GroupScheme.rationalPoints G))
        (↑s : Set (rationalNormKernelCompactInduction G π).representation.asModule) = ⊤} := by
  letI := finite_rationalNormKernelCompactInduction_of_finiteLength G π hfinite
  exact ⟨_, Classical.choose_spec (Module.finite_def.mp
    (inferInstance : Module.Finite (MonoidAlgebra ℂ (GroupScheme.rationalPoints G))
      (rationalNormKernelCompactInduction G π).representation.asModule))⟩

/-- Every finitely generated object of the actual lifted inertia block has
an integer-module Hom functor preserving all coproduct shapes in the target. -/
theorem rationalInertiaBlockHom_preservesCoproducts_of_finite
    (P : RationalInertiaBlock G (rationalInertiaBaseLift G π))
    [Module.Finite (MonoidAlgebra ℂ (GroupScheme.rationalPoints G))
      P.obj.representation.asModule]
    (I : Type (max uF uV)) :
    PreservesColimitsOfShape (Discrete I) (preadditiveCoyonedaInt P) := by
  apply SmoothRep.hom_preservesFullSubcategoryCoproducts
    (rationalInertiaBlockProperty G (rationalInertiaBaseLift G π))
  intro A d
  exact rationalInertiaBlockProperty_directSum G (rationalInertiaBaseLift G π)
    (fun i => (A i).obj) (fun i => (A i).property)

/-- For any proof of block membership, finite composition length of the
actual restriction gives the exact Hom coproduct-preservation conclusion. -/
theorem rationalNormKernelHom_preservesCoproducts_of_finiteLength
    (hfinite : IsFiniteLength (MonoidAlgebra ℂ (rationalCommonNormKernel G))
      (SmoothRep.restrictSubgroup (rationalCommonNormKernel G) π).representation.asModule)
    (hmem : rationalInertiaBlockProperty G (rationalInertiaBaseLift G π)
      (rationalNormKernelCompactInduction G π))
    (I : Type (max uF uV)) :
    let P : RationalInertiaBlock G (rationalInertiaBaseLift G π) :=
      ⟨rationalNormKernelCompactInduction G π, hmem⟩
    PreservesColimitsOfShape (Discrete I) (preadditiveCoyonedaInt P) := by
  let := finite_rationalNormKernelCompactInduction_of_finiteLength G π hfinite
  exact rationalInertiaBlockHom_preservesCoproducts_of_finite G π
    ⟨rationalNormKernelCompactInduction G π, hmem⟩ I

end Langlands.CuspidalSupport

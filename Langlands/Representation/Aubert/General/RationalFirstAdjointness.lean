import Langlands.Representation.Aubert.General.FirstAdjointnessConsequences
import Langlands.Representation.Aubert.General.RationalUnipotentRegularity

/-!
# Actual normalized first adjointness on standard rational points

The standard-cocharacter premise already present in the rational rank-one
targets supplies unimodularity. The group topology and all functors are the
literal ones used by those targets.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily.FirstAdjointness

open GroupScheme SmoothRep
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] [TopologicalSpace k]
  [ValuativeRel k] [IsNonarchimedeanLocalField k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance : TopologicalSpace (RationalPoint k G.X) := pointTopology

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)]
variable (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (hStandard : StandardCocharacterStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)
  (I : Finset (SimpleRoot i ν))
  (hU : IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))

local notation "h" =>
  isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν I

variable (A : SmoothRep.{0, _, v} ℂ (RationalPoint k G.X))
  (σ : SmoothRep.{0, _, w} ℂ (levi i ν I))

/-- The actual normalized first-adjointness equivalence at the canonical point
topology, without an additional unimodularity premise. -/
def equiv :
    (A.representation.IntertwiningMap
      ((normalizedInductionFunctor h hU).obj σ).representation) ≃ₗ[ℂ]
    (((jacquetFunctor h hU).obj A).representation.IntertwiningMap σ.representation) :=
  General.FirstAdjointness.equiv h hU
    (standardUnipotent_isUnimodular_of_standardCocharacterStatement
      i ν hStandard hG hi hν I hU) A σ

/-- On actual quotient generators, adjointness is evaluation at the identity. -/
@[simp] theorem equiv_evaluation
    (F : A.representation.IntertwiningMap
      ((normalizedInductionFunctor h hU).obj σ).representation) (a : A) :
    equiv i ν hStandard hG hi hν I hU A σ F
        (Jacquet.Localization.mk A.representation (unipotent i ν I) 1 a) =
      General.FirstAdjointness.evaluation h hU A σ F a :=
  rfl

/-- Evaluation of the inverse recovers the original Jacquet map on generators. -/
@[simp] theorem equiv_symm_evaluation
    (f : ((jacquetFunctor h hU).obj A).representation.IntertwiningMap σ.representation)
    (a : A) :
    General.FirstAdjointness.evaluation h hU A σ
        ((equiv i ν hStandard hG hi hν I hU A σ).symm f) a =
      f (Jacquet.Localization.mk A.representation (unipotent i ν I) 1 a) :=
  congrArg
    (fun t => t (Jacquet.Localization.mk A.representation (unipotent i ν I) 1 a))
    ((equiv i ν hStandard hG hi hν I hU A σ).apply_symm_apply f)

/-- Rational-point first adjointness is natural in its smooth source. -/
theorem equiv_comp {B : SmoothRep.{0, _, v} ℂ (RationalPoint k G.X)}
    (f : B ⟶ A)
    (F : A.representation.IntertwiningMap
      ((normalizedInductionFunctor h hU).obj σ).representation) :
    equiv i ν hStandard hG hi hν I hU B σ (F.comp (hom f)) =
      (equiv i ν hStandard hG hi hν I hU A σ F).comp
        (hom ((jacquetFunctor h hU).map f)) :=
  General.FirstAdjointness.equiv_comp h hU
    (standardUnipotent_isUnimodular_of_standardCocharacterStatement
      i ν hStandard hG hi hν I hU) A σ f F

/-- Every nonzero map into actual rational-point induction gives nonzero
actual normalized Jacquet restriction. -/
theorem nontrivial_jacquet_of_map_ne_zero
    (F : A.representation.IntertwiningMap
      ((normalizedInductionFunctor h hU).obj σ).representation) (hF : F ≠ 0) :
    Nontrivial ((jacquetFunctor h hU).obj A) :=
  General.FirstAdjointness.nontrivial_jacquet_of_map_ne_zero h hU
    (standardUnipotent_isUnimodular_of_standardCocharacterStatement
      i ν hStandard hG hi hν I hU) A σ F hF

/-- Every nontrivial subrepresentation of actual rational-point induction has
nonzero actual normalized Jacquet restriction at that standard Levi. -/
theorem nontrivial_jacquet_of_injective [Nontrivial A]
    (F : A.representation.IntertwiningMap
      ((normalizedInductionFunctor h hU).obj σ).representation)
    (hF : Function.Injective F) :
    Nontrivial ((jacquetFunctor h hU).obj A) :=
  General.FirstAdjointness.nontrivial_jacquet_of_injective h hU
    (standardUnipotent_isUnimodular_of_standardCocharacterStatement
      i ν hStandard hG hi hν I hU) A σ F hF

/-- For simple inducing data the actual adjoint is a quotient onto that data. -/
def quotientMapOfNonzero (hσ : σ.IsIrreducible)
    (F : A.representation.IntertwiningMap
      ((normalizedInductionFunctor h hU).obj σ).representation) (hF : F ≠ 0) :
    { f : ((jacquetFunctor h hU).obj A).representation.IntertwiningMap σ.representation //
      Function.Surjective f } :=
  General.FirstAdjointness.quotientMapOfNonzero h hU
    (standardUnipotent_isUnimodular_of_standardCocharacterStatement
      i ν hStandard hG hi hν I hU) A σ hσ F hF

/-- If the actual Jacquet module is also simple, the adjoint is an actual
representation equivalence, allowing independent carrier universes. -/
def equivalenceOfIrreducibleJacquet
    (hA : ((jacquetFunctor h hU).obj A).IsIrreducible) (hσ : σ.IsIrreducible)
    (F : A.representation.IntertwiningMap
      ((normalizedInductionFunctor h hU).obj σ).representation) (hF : F ≠ 0) :
    ((jacquetFunctor h hU).obj A).representation.Equiv σ.representation :=
  General.FirstAdjointness.equivalenceOfIrreducibleJacquet h hU
    (standardUnipotent_isUnimodular_of_standardCocharacterStatement
      i ν hStandard hG hi hν I hU) A σ hA hσ F hF

/-- At a common carrier universe, the same map gives the actual smooth-category
isomorphism required by object-level Jacquet conclusions. -/
def isoOfIrreducibleJacquet
    (τ : SmoothRep.{0, _, v} ℂ (levi i ν I))
    (hA : ((jacquetFunctor h hU).obj A).IsIrreducible) (hτ : τ.IsIrreducible)
    (F : A.representation.IntertwiningMap
      ((normalizedInductionFunctor h hU).obj τ).representation) (hF : F ≠ 0) :
    ((jacquetFunctor h hU).obj A) ≅ τ :=
  SmoothRep.mkIso
    (equivalenceOfIrreducibleJacquet i ν hStandard hG hi hν I hU A τ hA hτ F hF)

end Langlands.Aubert.General.RationalPointFamily.FirstAdjointness

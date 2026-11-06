import Langlands.Representation.Aubert.General.FullParabolicInductionFiniteLength
import Langlands.Representation.Aubert.General.RationalStandardInductionNonzero
import Langlands.Representation.CuspidalSupport.CuspidalTensorAssociationProof
import Langlands.Representation.Filtration.CentralEigenspaceSplitting
import Langlands.Representation.Exponents.ArbitraryParabolicInductionAdmissibility

/-! # Irreducibility of actual induction from a full parabolic -/

noncomputable section

universe uG uV u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General

section Generic

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] {P M U : Subgroup G}

/-- With continuous Levi projection, full-parabolic evaluation is surjective. -/
theorem fullParabolicEvaluation_surjective (h : IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set G)) (hP : ∀ g : G, g ∈ P)
    (hproj : Continuous h.projection) (A : SmoothRep.{0, uG, uV} ℂ M) :
    Function.Surjective (fullParabolicEvaluation h hU hP A) :=
  normalizedInduction_eval_surjective h hU hproj A

/-- Evaluation identifies actual full-parabolic induction with the normalized
inflated inducing action on the original carrier, read as an action of `G`. -/
def fullParabolicEvaluationEquiv (h : IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set G)) (hP : ∀ g : G, g ∈ P)
    (hproj : Continuous h.projection) (A : SmoothRep.{0, uG, uV} ℂ M) :
    ((normalizedInductionFunctor h hU).obj A).representation.Equiv
      ((inducingRepresentation h hU A).comp (fullParabolicInclusion hP)) :=
  (fullParabolicEvaluation h hU hP A).ofBijective
    ⟨fullParabolicEvaluation_injective h hU hP A,
      fullParabolicEvaluation_surjective h hU hP hproj A⟩

@[simp]
theorem fullParabolicEvaluationEquiv_apply (h : IsSemidirectDecomposition P M U)
    (hU : IsClosed (U : Set G)) (hP : ∀ g : G, g ∈ P)
    (hproj : Continuous h.projection) (A : SmoothRep.{0, uG, uV} ℂ M)
    (f : (normalizedInductionFunctor h hU).obj A) :
    fullParabolicEvaluationEquiv h hU hP hproj A f =
      Induction.eval P (inducingRepresentation h hU A) f 1 :=
  rfl

/-- The normalized inflated action of a full parabolic is irreducible whenever
the original Levi action is irreducible. -/
theorem inducingRepresentation_comp_fullParabolicInclusion_isIrreducible
    (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
    (hP : ∀ g : G, g ∈ P) (A : SmoothRep.{0, uG, uV} ℂ M)
    (hA : A.IsIrreducible) :
    Representation.IsIrreducible
      ((inducingRepresentation h hU A).comp (fullParabolicInclusion hP)) := by
  let : A.representation.IsIrreducible := hA
  have hproj : Function.Surjective h.projection :=
    fun m => ⟨⟨m, h.levi_le m.2⟩, h.projection_levi m⟩
  have hinfl := CuspidalSupport.isIrreducible_comp_of_surjective
    A.representation h.projection hproj
  have : (inducingRepresentation h hU A).IsIrreducible :=
    (isIrreducible_twist_iff _ _).mpr hinfl
  exact CuspidalSupport.isIrreducible_comp_of_surjective _
    (fullParabolicInclusion hP) (fullParabolicInclusion_surjective hP)

/-- Actual normalized induction from a full parabolic, with continuous Levi
projection, preserves irreducibility. -/
def FullParabolicInductionIrreducibleStatement : Prop :=
  ∀ (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
    (_hP : ∀ g : G, g ∈ P) (_hproj : Continuous h.projection)
    (A : SmoothRep.{0, uG, uV} ℂ M),
    A.IsIrreducible → ((normalizedInductionFunctor h hU).obj A).IsIrreducible

theorem fullParabolicInductionIrreducible :
    FullParabolicInductionIrreducibleStatement (P := P) (M := M) (U := U) := by
  intro h hU hP hproj A hA
  exact (CentralEigenspaceSplitting.isIrreducible_iff_of_equiv
    (fullParabolicEvaluationEquiv h hU hP hproj A)).mpr
      (inducingRepresentation_comp_fullParabolicInclusion_isIrreducible h hU hP A hA)

end Generic

namespace RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k]
  {G P M U : GroupScheme (Spec (CommRingCat.of k))}

/-- An isomorphic represented parabolic contains every ambient rational point. -/
theorem mem_pointImage_of_isIso (p : P ⟶ G) [IsIso p] (g : rationalPoints G) :
    g ∈ pointImage p := by
  refine ⟨rationalPoints.map (inv p) g, ?_⟩
  rw [← pointMap_comp_apply, IsIso.inv_hom_id]
  rfl

variable [TopologicalSpace k] [T2Space k] [IsAffineHom G.X.hom]

local instance fullInductionPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]

/-- Induction from a full represented parabolic preserves irreducibility for
representations of the Levi's own point group. -/
theorem leviInduction_isIrreducible_of_isIso
    (p : P ⟶ G) [IsIso p] (l : M ⟶ P) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
    (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hmul : IsIso (subgroupMultiplication l r))
    (A : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (hA : letI := leviPointTopology l hl; A.IsIrreducible) :
    letI := leviPointTopology l hl
    ((leviInductionFunctor p l r hp hr hl hmul).obj A).IsIrreducible := by
  let := leviPointTopology l hl
  let : A.representation.IsIrreducible := hA
  have hin : (SmoothRep.pullback (leviPointsEquiv p l hp hl).symm A).IsIrreducible :=
    CuspidalSupport.isIrreducible_comp_of_surjective A.representation
      (leviPointsEquiv p l hp hl).symm.toMonoidHom
      (leviPointsEquiv p l hp hl).symm.surjective
  exact fullParabolicInductionIrreducible
    (isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul)
    (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
    (mem_pointImage_of_isIso p)
    (continuous_projection_pointImage p l r hp hl hr hmul)
    (SmoothRep.pullback (leviPointsEquiv p l hp hl).symm A) hin

end RepresentedParabolic

end Langlands.Aubert.General

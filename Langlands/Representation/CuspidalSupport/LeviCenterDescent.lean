import Langlands.CategoryTheory.FaithfulCenterDescent
import Langlands.Representation.CuspidalSupport.LeviInductionEndEmbedding
import Langlands.Representation.Exponents.LeviRadicalCompactSubgroups
import Langlands.Representation.Aubert.General.InductionLimits
import Langlands.Representation.Aubert.General.CuspidalRemainderTransport

/-! # Center descent and first adjointness for actual rational Levi functors -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G P M U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance centerDescentAmbientTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
  (hp : IsParabolicSubgroup p) (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hl : IsRationalLeviSubgroup l) (hmul : IsIso (subgroupMultiplication l r))

/-- The first adjunction on the rational points of an actual Levi, on carriers
in the common universe `max u v`. Radical unimodularity is proved unconditionally. -/
def leviFirstAdjunction :
    letI := leviPointTopology l hl
    leviJacquetFunctor.{u, max u v} p l r hp hr hl hmul ⊣
      leviInductionFunctor.{u, max u v} p l r hp hr hl hmul := by
  letI := leviPointTopology l hl
  exact (firstAdjointnessAdjunction
    (isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul)
    (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
    (isUnimodularModulus_pointImage_radical p r hp.isClosedSubgroup hr.1)).comp
      (SmoothRep.pullbackEquivalence (leviPointsEquiv p l hp hl)).toAdjunction

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/-- Actual normalized induction is additive on morphisms. -/
theorem leviInductionFunctor_additive :
    letI := leviPointTopology l hl
    (leviInductionFunctor.{u, v} p l r hp hr hl hmul).Additive where
  map_add := by
    intros
    ext f
    rfl

/-- Pointwise lifts of central components for actual induction determine a
center ring homomorphism. Existence of the lifts remains an explicit premise. -/
def leviCenterDescent :
    letI := leviPointTopology l hl
    Renard.CenterComponentsLift (leviInductionFunctor.{u, max u v} p l r hp hr hl hmul) →
      CatCenter (SmoothRep.{0, u, max u v} ℂ (rationalPoints G)) →+*
        CatCenter (SmoothRep.{0, u, max u v} ℂ (rationalPoints M)) := by
  letI := leviPointTopology l hl
  letI := leviInductionFunctor_faithful.{u, max u v} p l r hp hr hl hmul
  letI := leviInductionFunctor_additive.{u, max u v} p l r hp hr hl hmul
  exact Renard.faithfulCenterDescent _

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
@[simp]
theorem leviCenterDescent_induction :
    letI := leviPointTopology l hl
    ∀ (h : Renard.CenterComponentsLift (leviInductionFunctor.{u, max u v} p l r hp hr hl hmul))
      (z : CatCenter (SmoothRep.{0, u, max u v} ℂ (rationalPoints G)))
      (σ : SmoothRep.{0, u, max u v} ℂ (rationalPoints M)),
      (leviInductionFunctor p l r hp hr hl hmul).map
          ((leviCenterDescent p l r hp hr hl hmul h z).app σ) =
        z.app ((leviInductionFunctor p l r hp hr hl hmul).obj σ) := by
  let := leviPointTopology l hl
  let := leviInductionFunctor_faithful.{u, max u v} p l r hp hr hl hmul
  let := leviInductionFunctor_additive.{u, max u v} p l r hp hr hl hmul
  exact Renard.faithfulCenterDescent_map_app _

/-- Induction compatibility for the descended center map implies Jacquet
compatibility by the actual first adjunction. -/
theorem leviCenterDescent_jacquet :
    letI := leviPointTopology l hl
    ∀ (h : Renard.CenterComponentsLift (leviInductionFunctor.{u, max u v} p l r hp hr hl hmul))
      (z : CatCenter (SmoothRep.{0, u, max u v} ℂ (rationalPoints G)))
      (π : SmoothRep.{0, u, max u v} ℂ (rationalPoints G)),
      (leviJacquetFunctor p l r hp hr hl hmul).map (z.app π) =
        (leviCenterDescent p l r hp hr hl hmul h z).app
          ((leviJacquetFunctor p l r hp hr hl hmul).obj π) := by
  let := leviPointTopology l hl
  let := leviInductionFunctor_faithful.{u, max u v} p l r hp hr hl hmul
  let := leviInductionFunctor_additive.{u, max u v} p l r hp hr hl hmul
  intro h z π
  exact Renard.faithfulCenterDescent_leftAdjoint _ h
    (leviFirstAdjunction p l r hp hr hl hmul) z π

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/-- Any actual Levi center map satisfying induction compatibility is the
descended one; hence it is uniquely determined by that compatibility. -/
theorem leviCenterDescent_unique :
    letI := leviPointTopology l hl
    ∀ (h : Renard.CenterComponentsLift (leviInductionFunctor.{u, max u v} p l r hp hr hl hmul))
      (φ : CatCenter (SmoothRep.{0, u, max u v} ℂ (rationalPoints G)) →+*
        CatCenter (SmoothRep.{0, u, max u v} ℂ (rationalPoints M))),
      (∀ (z : CatCenter (SmoothRep.{0, u, max u v} ℂ (rationalPoints G)))
        (σ : SmoothRep.{0, u, max u v} ℂ (rationalPoints M)),
        (leviInductionFunctor p l r hp hr hl hmul).map ((φ z).app σ) =
          z.app ((leviInductionFunctor p l r hp hr hl hmul).obj σ)) →
      φ = leviCenterDescent p l r hp hr hl hmul h := by
  let := leviPointTopology l hl
  let := leviInductionFunctor_faithful.{u, max u v} p l r hp hr hl hmul
  let := leviInductionFunctor_additive.{u, max u v} p l r hp hr hl hmul
  exact Renard.faithfulCenterDescent_unique _

end Langlands.Aubert.General.RepresentedParabolic

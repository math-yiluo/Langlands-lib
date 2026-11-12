import Langlands.Representation.Induction.Faithful
import Langlands.Representation.Exponents.ArbitraryParabolicInductionAdmissibility

/-! # The faithful induction embedding on actual rational Levi endomorphisms -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [TopologicalSpace k]
  {G P M U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance inductionFaithfulPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [T2Space k] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)]

/-- Normalized induction from the rational points of an actual rational Levi is
faithful, with no restriction on smooth representations or their carrier universe. -/
theorem leviInductionFunctor_faithful (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hl : IsRationalLeviSubgroup l) (hmul : IsIso (subgroupMultiplication l r)) :
    letI := leviPointTopology l hl
    (leviInductionFunctor.{u, v} p l r hp hr hl hmul).Faithful := by
  let := leviPointTopology l hl
  let : (inductionFunctor.{u, v} p l r hp hr hl hmul).Faithful :=
    normalizedInductionFunctor_faithful
      (isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul)
      (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
      (continuous_projection_pointImage p l r hp hl hr hmul)
  constructor
  intro A B f g hfg
  have he : (SmoothRep.pullbackFunctor (leviPointsEquiv p l hp hl).symm).map f =
      (SmoothRep.pullbackFunctor (leviPointsEquiv p l hp hl).symm).map g :=
    (inductionFunctor p l r hp hr hl hmul).map_injective hfg
  ext v
  exact congrArg (fun a :
      (SmoothRep.pullbackFunctor (leviPointsEquiv p l hp hl).symm).obj A ⟶
        (SmoothRep.pullbackFunctor (leviPointsEquiv p l hp hl).symm).obj B =>
      SmoothRep.hom a v) he

/-- The injective endomorphism map `a ↦ i_P^G(a)` of VI.10.4, for every smooth
coefficient object, as an actual function embedding. -/
def leviInductionEndEmbedding (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hl : IsRationalLeviSubgroup l) (hmul : IsIso (subgroupMultiplication l r)) :
    letI := leviPointTopology l hl
    (σ : SmoothRep.{0, u, v} ℂ (rationalPoints M)) →
      End σ ↪ End ((leviInductionFunctor p l r hp hr hl hmul).obj σ) := by
  letI := leviPointTopology l hl
  letI := leviInductionFunctor_faithful.{u, v} p l r hp hr hl hmul
  intro σ
  exact ⟨fun a => (leviInductionFunctor p l r hp hr hl hmul).map a,
    (leviInductionFunctor p l r hp hr hl hmul).map_injective⟩

@[simp]
theorem leviInductionEndEmbedding_apply (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (hp : IsParabolicSubgroup p) (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hl : IsRationalLeviSubgroup l) (hmul : IsIso (subgroupMultiplication l r)) :
    letI := leviPointTopology l hl
    ∀ (σ : SmoothRep.{0, u, v} ℂ (rationalPoints M)) (a : End σ),
      leviInductionEndEmbedding p l r hp hr hl hmul σ a =
        (leviInductionFunctor p l r hp hr hl hmul).map a := by
  intros
  rfl

end Langlands.Aubert.General.RepresentedParabolic

import Langlands.Representation.Exponents.LeviParabolicFunctorsExactProof
import Langlands.Representation.Aubert.General.InductionEmbeddings
import Langlands.Representation.Smooth.FiniteLengthInduction

/-! # Embeddings under induction from an actual represented Levi -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G P M U : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom M.X.hom]

local instance leviInductionEmbeddingAmbientTopology :
    TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)]
  (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
  (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
  (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hmul : IsIso (subgroupMultiplication l r))

local instance leviInductionEmbeddingSourceTopology :
    TopologicalSpace (rationalPoints M) := RationalPointFamily.pointTopology

/-- Postcompose actual represented-Levi induced functions with a coefficient
intertwiner, allowing independent coefficient carrier universes. -/
def leviInductionMap
    {A : SmoothRep.{0, u, v} ℂ (rationalPoints M)}
    {B : SmoothRep.{0, u, w} ℂ (rationalPoints M)}
    (f : A.representation.IntertwiningMap B.representation) :
    ((leviInductionFunctor.{u, v} p l r hp hr hl hmul).obj A).representation.IntertwiningMap
      ((leviInductionFunctor.{u, w} p l r hp hr hl hmul).obj B).representation :=
  normalizedInductionMap
    (isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul)
    (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
    (A := SmoothRep.pullback (leviPointsEquiv p l hp hl).symm A)
    (B := SmoothRep.pullback (leviPointsEquiv p l hp hl).symm B)
    { toLinearMap := f.toLinearMap
      isIntertwining' m := f.isIntertwining' ((leviPointsEquiv p l hp hl).symm m) }

/-- At one carrier universe this is exactly the map of the published functor. -/
@[simp]
theorem leviInductionMap_hom
    {A B : SmoothRep.{0, u, v} ℂ (rationalPoints M)} (f : A ⟶ B) :
    leviInductionMap p l r hp hl hr hmul (SmoothRep.hom f) =
      SmoothRep.hom ((leviInductionFunctor p l r hp hr hl hmul).map f) := rfl

/-- The induced intertwiner is injective whenever the coefficient map is. -/
theorem leviInductionMap_injective
    {A : SmoothRep.{0, u, v} ℂ (rationalPoints M)}
    {B : SmoothRep.{0, u, w} ℂ (rationalPoints M)}
    (f : A.representation.IntertwiningMap B.representation)
    (hf : Function.Injective f) :
    Function.Injective (leviInductionMap p l r hp hl hr hmul f) :=
  normalizedInductionMap_injective _ _ _ hf

/-- Finite group-algebra length descends along an induced embedding, with no
common carrier-universe restriction on its coefficients. -/
theorem leviInduction_hasFiniteLength_of_injective
    {A : SmoothRep.{0, u, v} ℂ (rationalPoints M)}
    {B : SmoothRep.{0, u, w} ℂ (rationalPoints M)}
    (f : A.representation.IntertwiningMap B.representation)
    (hf : Function.Injective f)
    (hB : ((leviInductionFunctor.{u, w} p l r hp hr hl hmul).obj B).HasFiniteLength) :
    ((leviInductionFunctor.{u, v} p l r hp hr hl hmul).obj A).HasFiniteLength :=
  IsFiniteLength.of_injective hB
    (f := Representation.IntertwiningMap.equivLinearMapAsModule _ _
      (leviInductionMap p l r hp hl hr hmul f))
    (leviInductionMap_injective p l r hp hl hr hmul f hf)

/-- For the actual induction functor, the irreducible finite-length case
suffices: its required short-exact-sequence preservation is already proved. -/
theorem leviInduction_preservesFiniteLength_of_irreducibles
    [ValuativeRel k] [IsNonarchimedeanLocalField k]
    (hG : IsConnectedReductive G)
    (hirr : ∀ A : SmoothRep.{0, u, v} ℂ (rationalPoints M),
      A.IsIrreducible →
        ((leviInductionFunctor.{u, v} p l r hp hr hl hmul).obj A).HasFiniteLength) :
    SmoothRep.PreservesFiniteLength (leviInductionFunctor.{u, v} p l r hp hr hl hmul) := by
  apply SmoothRep.preservesFiniteLength_of_irreducibles _ _ hirr
  intro A B C f g _ _ _ hfg
  exact (leviParabolicFunctorsExact k G hG P M U p l r hp hl hr hmul).1 f g hfg

end Langlands.Aubert.General.RepresentedParabolic

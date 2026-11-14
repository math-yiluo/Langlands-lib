import Langlands.Geometry.Building.Kottwitz.FundamentalGroupStatement
import Langlands.GroupScheme.AlgebraicFundamentalGroupComparisonProof
import Langlands.GroupScheme.AlgebraicFundamentalGroupMapNaturality
import Langlands.GroupScheme.AlgebraicFundamentalGroupFunctorProof

/-! # Descent of fundamental-group maps to inertia coinvariants -/

noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme
open Langlands.GroupScheme.AlgebraicFundamentalGroup

namespace Langlands.Geometry.Building.Kottwitz

section Descent

variable (k K E : Type u) [Field k] [Field K] [Field E]
  [Algebra k K] [Algebra k E] [Algebra K E] [IsScalarTower k K E]
  [Normal k K]
  (H G : GroupScheme (Spec (CommRingCat.of k)))
  (hH : IsConnectedReductive H) (hG : IsConnectedReductive G) (f : H ⟶ G)

/-- Every inertia class has a representative in the original fundamental group. -/
theorem fundamentalInertiaProjection_surjective :
    Function.Surjective (fundamentalInertiaProjection k K E H hH) :=
  Representation.Coinvariants.mk_surjective _

/-- The representative law determines the descended map. -/
theorem isFundamentalInertiaMap_unique
    {m n : FundamentalInertia k K E H hH →ₗ[ℤ] FundamentalInertia k K E G hG}
    (hm : IsFundamentalInertiaMap k K E G hG H hH f m)
    (hn : IsFundamentalInertiaMap k K E G hG H hH f n) : m = n := by
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := fundamentalInertiaProjection_surjective k K E H hH x
  exact (hm y).trans (hn y).symm

/-- Equivariance of the original map supplies its unique inertia descent. -/
theorem fundamentalInertiaMap_existsUnique_of_equivariant
    (hf : ∀ (σ : E ≃ₐ[k] E) (x : fundamentalGroup k H E hH),
      fundamentalGroupMap k E H G hH hG f (fundamentalGroupGalois k H E hH σ x) =
        fundamentalGroupGalois k G E hG σ (fundamentalGroupMap k E H G hH hG f x)) :
    ∃! m, IsFundamentalInertiaMap k K E G hG H hH f m := by
  let m : FundamentalInertia k K E H hH →ₗ[ℤ] FundamentalInertia k K E G hG :=
    Representation.Coinvariants.lift _
      ((fundamentalInertiaProjection k K E G hG).comp
        (fundamentalGroupMap k E H G hH hG f)) (fun σ => by
          apply LinearMap.ext
          intro x
          change fundamentalInertiaProjection k K E G hG
            (fundamentalGroupMap k E H G hH hG f
              (fundamentalGroupGalois k H E hH σ.val x)) =
            fundamentalInertiaProjection k K E G hG
              (fundamentalGroupMap k E H G hH hG f x)
          rw [hf]
          exact Representation.Coinvariants.mk_self_apply _ σ _)
  have hm : IsFundamentalInertiaMap k K E G hG H hH f m := fun _ => rfl
  exact ⟨m, hm, fun n hn => isFundamentalInertiaMap_unique k K E H G hH hG f hn hm⟩

/-- Existence justifies the epsilon-selected map's representative law. -/
theorem fundamentalInertiaMap_spec_of_exists
    (h : ∃ m, IsFundamentalInertiaMap k K E G hG H hH f m) :
    IsFundamentalInertiaMap k K E G hG H hH f
      (fundamentalInertiaMap k K E G hG H hH f) :=
  Classical.epsilon_spec h

variable [Normal k E]

/-- Residual equivariance follows by lifting an automorphism of `K` and a
representative of an inertia class. -/
theorem isFundamentalInertiaMap_residual_equivariant
    {m : FundamentalInertia k K E H hH →ₗ[ℤ] FundamentalInertia k K E G hG}
    (hm : IsFundamentalInertiaMap k K E G hG H hH f m)
    (hf : ∀ (σ : E ≃ₐ[k] E) (x : fundamentalGroup k H E hH),
      fundamentalGroupMap k E H G hH hG f (fundamentalGroupGalois k H E hH σ x) =
        fundamentalGroupGalois k G E hG σ (fundamentalGroupMap k E H G hH hG f x))
    (σ : K ≃ₐ[k] K) (x : FundamentalInertia k K E H hH) :
    m (fundamentalGammaRepresentation k K E H hH σ x) =
      fundamentalGammaRepresentation k K E G hG σ (m x) := by
  obtain ⟨τ, hτ⟩ := AlgEquiv.restrictNormalHom_surjective (F := k) (E := E) (K₁ := K) σ
  change τ.restrictNormal K = σ at hτ
  rw [← hτ]
  obtain ⟨y, rfl⟩ := fundamentalInertiaProjection_surjective k K E H hH x
  rw [inertiaGammaRepresentation_restrict, hm, hm, inertiaGammaRepresentation_restrict, hf]

end Descent

/-- The quotient argument reduces inertia functoriality to the original
fundamental-group functor laws. -/
theorem fundamentalInertiaMap_of_fundamentalGroup
    (hfunctor : AlgebraicFundamentalGroupFunctorStatement.{u}) :
    FundamentalInertiaMapStatement.{u} := by
  have hcomparison : AlgebraicFundamentalGroupComparisonStatement.{u} :=
    algebraicFundamentalGroupComparison
  have hmap : AlgebraicFundamentalGroupMapStatement.{u} :=
    algebraicFundamentalGroupMap_of_comparison hcomparison
  intro k K E _ _ _ _ _ _ _ _ _ _
  have heq (H G : GroupScheme (Spec (CommRingCat.of k)))
      (hH : IsConnectedReductive H) (hG : IsConnectedReductive G) (f : H ⟶ G) :
      ∀ (σ : E ≃ₐ[k] E) (x : fundamentalGroup k H E hH),
        fundamentalGroupMap k E H G hH hG f (fundamentalGroupGalois k H E hH σ x) =
          fundamentalGroupGalois k G E hG σ (fundamentalGroupMap k E H G hH hG f x) :=
    (hmap k E H G hH hG (chosenChoice k H hH) (chosenChoice k G hG) f).2.2.1
  have hspec (H G : GroupScheme (Spec (CommRingCat.of k)))
      (hH : IsConnectedReductive H) (hG : IsConnectedReductive G) (f : H ⟶ G) :
      IsFundamentalInertiaMap k K E G hG H hH f
        (fundamentalInertiaMap k K E G hG H hH f) :=
    fundamentalInertiaMap_spec_of_exists k K E H G hH hG f
      (fundamentalInertiaMap_existsUnique_of_equivariant k K E H G hH hG f
        (heq H G hH hG f)).exists
  refine ⟨?_, ?_, ?_⟩
  · intro H G hH hG f
    exact ⟨fundamentalInertiaMap_existsUnique_of_equivariant k K E H G hH hG f
        (heq H G hH hG f),
      hspec H G hH hG f,
      isFundamentalInertiaMap_residual_equivariant k K E H G hH hG f
        (hspec H G hH hG f) (heq H G hH hG f)⟩
  · intro G hG
    have hid : fundamentalGroupMap k E G G hG hG (𝟙 G) = LinearMap.id :=
      ((hfunctor k E).1 G hG (chosenChoice k G hG) (chosenChoice k G hG)).trans
        ((hcomparison k E G hG).2.1 (chosenChoice k G hG))
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := fundamentalInertiaProjection_surjective k K E G hG x
    change fundamentalInertiaMap k K E G hG G hG (𝟙 G)
      (fundamentalInertiaProjection k K E G hG y) =
        fundamentalInertiaProjection k K E G hG y
    rw [hspec, hid]
    rfl
  · intro H G J hH hG hJ f g
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := fundamentalInertiaProjection_surjective k K E H hH x
    change fundamentalInertiaMap k K E J hJ G hG g
      (fundamentalInertiaMap k K E G hG H hH f
        (fundamentalInertiaProjection k K E H hH y)) =
      fundamentalInertiaMap k K E J hJ H hH (f ≫ g)
        (fundamentalInertiaProjection k K E H hH y)
    rw [hspec, hspec, hspec]
    exact congrArg (fun m => fundamentalInertiaProjection k K E J hJ (m y))
      ((hfunctor k E).2 H G J hH hG hJ
        (chosenChoice k H hH) (chosenChoice k G hG) (chosenChoice k J hJ) f g)

/-- Fundamental-group maps descend uniquely to inertia coinvariants, commute
with the residual Galois action, and preserve identities and composition. -/
theorem fundamentalInertiaMapStatement : FundamentalInertiaMapStatement.{u} :=
  fundamentalInertiaMap_of_fundamentalGroup algebraicFundamentalGroupFunctor

end Langlands.Geometry.Building.Kottwitz

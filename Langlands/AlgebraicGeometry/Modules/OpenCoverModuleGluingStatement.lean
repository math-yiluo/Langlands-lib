import Langlands.AlgebraicGeometry.Modules.SquarePullbackComparison
import Mathlib.AlgebraicGeometry.Cover.Open

/-! # Gluing actual module sheaves over an arbitrary scheme open cover -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.Scheme.Modules

/-- Module sheaves on the members of an arbitrary open cover, with isomorphisms
of their actual pullbacks to the pairwise overlaps satisfying the cocycle
condition on the triple overlaps, glue to an actual module sheaf on the whole
scheme. Its actual pullback to each member is identified with the given piece,
and these identifications are compatible with the overlap isomorphisms. -/
def OpenCoverModuleGluingStatement : Prop :=
  ∀ (X : AlgebraicGeometry.Scheme.{u}) (𝒰 : X.OpenCover.{u})
    (M : ∀ i, (𝒰.X i).Modules)
    (φ : ∀ i j,
      (AlgebraicGeometry.Scheme.Modules.pullback (pullback.fst (𝒰.f i) (𝒰.f j))).obj (M i) ≅
        (AlgebraicGeometry.Scheme.Modules.pullback (pullback.snd (𝒰.f i) (𝒰.f j))).obj (M j)),
    (∀ i j k,
      (AlgebraicGeometry.Scheme.Modules.pullback
          (pullback.fst (pullback.fst (𝒰.f i) (𝒰.f j))
            (pullback.fst (𝒰.f i) (𝒰.f k)))).map (φ i j).hom ≫
        (squarePullbackIso (pullback.fst (𝒰.f j) (𝒰.f k))
          (pullback.fst (pullback.fst (𝒰.f i) (𝒰.f j)) (pullback.fst (𝒰.f i) (𝒰.f k)))
          (pullback.lift
            (pullback.fst (pullback.fst (𝒰.f i) (𝒰.f j)) (pullback.fst (𝒰.f i) (𝒰.f k)) ≫
              pullback.snd (𝒰.f i) (𝒰.f j))
            (pullback.snd (pullback.fst (𝒰.f i) (𝒰.f j)) (pullback.fst (𝒰.f i) (𝒰.f k)) ≫
              pullback.snd (𝒰.f i) (𝒰.f k))
            (by simp only [Category.assoc, ← pullback.condition, pullback.condition_assoc]))
          (pullback.snd (𝒰.f i) (𝒰.f j)) (pullback.lift_fst _ _ _).symm (M j)).hom ≫
        (AlgebraicGeometry.Scheme.Modules.pullback
          (pullback.lift
            (pullback.fst (pullback.fst (𝒰.f i) (𝒰.f j)) (pullback.fst (𝒰.f i) (𝒰.f k)) ≫
              pullback.snd (𝒰.f i) (𝒰.f j))
            (pullback.snd (pullback.fst (𝒰.f i) (𝒰.f j)) (pullback.fst (𝒰.f i) (𝒰.f k)) ≫
              pullback.snd (𝒰.f i) (𝒰.f k))
            (by simp only [Category.assoc, ← pullback.condition, pullback.condition_assoc]))).map
          (φ j k).hom ≫
        (squarePullbackIso (pullback.snd (𝒰.f i) (𝒰.f k))
          (pullback.lift
            (pullback.fst (pullback.fst (𝒰.f i) (𝒰.f j)) (pullback.fst (𝒰.f i) (𝒰.f k)) ≫
              pullback.snd (𝒰.f i) (𝒰.f j))
            (pullback.snd (pullback.fst (𝒰.f i) (𝒰.f j)) (pullback.fst (𝒰.f i) (𝒰.f k)) ≫
              pullback.snd (𝒰.f i) (𝒰.f k))
            (by simp only [Category.assoc, ← pullback.condition, pullback.condition_assoc]))
          (pullback.snd (pullback.fst (𝒰.f i) (𝒰.f j)) (pullback.fst (𝒰.f i) (𝒰.f k)))
          (pullback.snd (𝒰.f j) (𝒰.f k)) (pullback.lift_snd _ _ _) (M k)).hom =
      (squarePullbackIso (pullback.fst (𝒰.f i) (𝒰.f k))
          (pullback.fst (pullback.fst (𝒰.f i) (𝒰.f j)) (pullback.fst (𝒰.f i) (𝒰.f k)))
          (pullback.snd (pullback.fst (𝒰.f i) (𝒰.f j)) (pullback.fst (𝒰.f i) (𝒰.f k)))
          (pullback.fst (𝒰.f i) (𝒰.f j)) pullback.condition (M i)).hom ≫
        (AlgebraicGeometry.Scheme.Modules.pullback
          (pullback.snd (pullback.fst (𝒰.f i) (𝒰.f j))
            (pullback.fst (𝒰.f i) (𝒰.f k)))).map (φ i k).hom) →
    ∃ (N : X.Modules)
      (ψ : ∀ i, (AlgebraicGeometry.Scheme.Modules.pullback (𝒰.f i)).obj N ≅ M i),
      ∀ i j,
        (AlgebraicGeometry.Scheme.Modules.pullback
            (pullback.fst (𝒰.f i) (𝒰.f j))).map (ψ i).hom ≫ (φ i j).hom =
          (squarePullbackIso (𝒰.f j) (pullback.fst (𝒰.f i) (𝒰.f j))
            (pullback.snd (𝒰.f i) (𝒰.f j)) (𝒰.f i) pullback.condition N).hom ≫
            (AlgebraicGeometry.Scheme.Modules.pullback
              (pullback.snd (𝒰.f i) (𝒰.f j))).map (ψ j).hom

end Langlands.Scheme.Modules

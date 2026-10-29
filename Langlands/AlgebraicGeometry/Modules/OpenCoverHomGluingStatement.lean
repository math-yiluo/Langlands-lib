import Langlands.AlgebraicGeometry.Modules.SquarePullbackComparison
import Mathlib.AlgebraicGeometry.Cover.Open

/-! # Gluing actual module morphisms over an arbitrary scheme open cover -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.Scheme.Modules

/-- Compatible maps between the actual pullbacks of two fixed module sheaves
glue uniquely over an arbitrary open cover. -/
def OpenCoverHomGluingStatement : Prop :=
  ∀ (X : AlgebraicGeometry.Scheme.{u}) (𝒰 : X.OpenCover.{u}) (M N : X.Modules)
    (φ : ∀ i,
      (AlgebraicGeometry.Scheme.Modules.pullback (𝒰.f i)).obj M ⟶
        (AlgebraicGeometry.Scheme.Modules.pullback (𝒰.f i)).obj N),
    (∀ i j,
      (AlgebraicGeometry.Scheme.Modules.pullback
        (pullback.fst (𝒰.f i) (𝒰.f j))).map (φ i) ≫
          (squarePullbackIso (𝒰.f j) (pullback.fst (𝒰.f i) (𝒰.f j))
            (pullback.snd (𝒰.f i) (𝒰.f j)) (𝒰.f i) pullback.condition N).hom =
      (squarePullbackIso (𝒰.f j) (pullback.fst (𝒰.f i) (𝒰.f j))
        (pullback.snd (𝒰.f i) (𝒰.f j)) (𝒰.f i) pullback.condition M).hom ≫
          (AlgebraicGeometry.Scheme.Modules.pullback
            (pullback.snd (𝒰.f i) (𝒰.f j))).map (φ j)) →
    ∃! f : M ⟶ N, ∀ i,
      (AlgebraicGeometry.Scheme.Modules.pullback (𝒰.f i)).map f = φ i

end Langlands.Scheme.Modules

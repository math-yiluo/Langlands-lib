import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Descent of finitely presented modules to finitely generated subalgebras -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.NoetherianApproximation

/-- Over a noetherian ring `A₀`, a locally finitely presented module sheaf on a base change `X`
to `Spec A` of a quasi-compact separated morphism `X₀ ⟶ Spec A₀` of finite type comes, up to
isomorphism, from a locally finitely presented module sheaf on the chosen base change of `X₀`
to `Spec T`, for a finitely generated `A₀`-subalgebra `T` of `A` containing any given finite
set. The comparison holds along every morphism `c` from `X` to that chosen base change
compatible with both projections. -/
def FinitePresentationModuleSubalgebraDescentStatement : Prop :=
  ∀ {A₀ : Type u} [CommRing A₀] [IsNoetherianRing A₀] {A : Type u} [CommRing A] [Algebra A₀ A]
    {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ Spec (CommRingCat.of A₀)) [QuasiCompact f₀]
    [IsSeparated f₀] [LocallyOfFiniteType f₀] {X : Scheme.{u}} (a : X ⟶ X₀)
    (f : X ⟶ Spec (CommRingCat.of A)),
    IsPullback a f f₀ (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))) →
    ∀ (M : X.Modules), M.IsFinitePresentation → ∀ (s : Finset A),
    ∃ (T : Subalgebra A₀ A), T.FG ∧ (↑s : Set A) ⊆ T ∧
      ∃ (M₀ : (pullback f₀ (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T)))).Modules),
        M₀.IsFinitePresentation ∧
        ∀ c : X ⟶ pullback f₀ (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))),
          c ≫ pullback.fst _ _ = a →
          c ≫ pullback.snd _ _ = f ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥T A)) →
          Nonempty ((Scheme.Modules.pullback c).obj M₀ ≅ M)

end Langlands.AlgebraicGeometry.NoetherianApproximation

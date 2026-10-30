import Langlands.AlgebraicGeometry.Picard.LineBundle
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Descent of line bundles and their isomorphisms to finitely generated subalgebras -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.NoetherianApproximation

open Langlands.AlgebraicGeometry.Picard

/-- A locally free rank-one module on a base change `X` to `Spec A` of a quasi-compact,
quasi-separated scheme `X₀` over `Spec A₀` comes, up to isomorphism, from a locally free
rank-one module on the chosen base change of `X₀` to `Spec T`, for a finitely generated
`A₀`-subalgebra `T` of `A` containing any given finite set. The comparison holds along every
morphism `c` from `X` to that chosen base change compatible with both projections. -/
def LineBundleSubalgebraDescentStatement : Prop :=
  ∀ {A₀ : Type u} [CommRing A₀] {A : Type u} [CommRing A] [Algebra A₀ A]
    {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ Spec (CommRingCat.of A₀)) [QuasiCompact f₀]
    [QuasiSeparated f₀] {X : Scheme.{u}} (a : X ⟶ X₀) (f : X ⟶ Spec (CommRingCat.of A)),
    IsPullback a f f₀ (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))) →
    ∀ (M : X.Modules), IsLocallyFreeRankOne M → ∀ (s : Finset A),
    ∃ (T : Subalgebra A₀ A), T.FG ∧ (↑s : Set A) ⊆ T ∧
      ∃ (M₀ : (pullback f₀ (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T)))).Modules),
        IsLocallyFreeRankOne M₀ ∧
        ∀ c : X ⟶ pullback f₀ (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))),
          c ≫ pullback.fst _ _ = a →
          c ≫ pullback.snd _ _ = f ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥T A)) →
          Nonempty ((Scheme.Modules.pullback c).obj M₀ ≅ M)

/-- Two locally free rank-one modules on a quasi-compact, quasi-separated scheme `X₀` over
`Spec A₀` that become isomorphic after base change to `Spec A` already become isomorphic after
base change to `Spec T`, for a finitely generated `A₀`-subalgebra `T` of `A` containing any
given finite set. The conclusion holds for every pullback square over `Spec T`. -/
def LineBundleIsoSubalgebraDescentStatement : Prop :=
  ∀ {A₀ : Type u} [CommRing A₀] {A : Type u} [CommRing A] [Algebra A₀ A]
    {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ Spec (CommRingCat.of A₀)) [QuasiCompact f₀]
    [QuasiSeparated f₀] (M N : X₀.Modules), IsLocallyFreeRankOne M → IsLocallyFreeRankOne N →
    ∀ {X : Scheme.{u}} (a : X ⟶ X₀) (f : X ⟶ Spec (CommRingCat.of A)),
    IsPullback a f f₀ (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))) →
    Nonempty ((Scheme.Modules.pullback a).obj M ≅ (Scheme.Modules.pullback a).obj N) →
    ∀ (s : Finset A),
    ∃ (T : Subalgebra A₀ A), T.FG ∧ (↑s : Set A) ⊆ T ∧
      ∀ {X' : Scheme.{u}} (a' : X' ⟶ X₀) (f' : X' ⟶ Spec (CommRingCat.of ↥T)),
        IsPullback a' f' f₀ (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))) →
        Nonempty ((Scheme.Modules.pullback a').obj M ≅ (Scheme.Modules.pullback a').obj N)

end Langlands.AlgebraicGeometry.NoetherianApproximation

import Langlands.AlgebraicGeometry.Modules.DerivedSections

/-! # Pushforwards of injective scheme modules are acyclic for global sections -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules

/-- For every morphism of schemes `h : X ⟶ Y` and every injective `𝒪_X`-module `J`,
the pushforward `h_* J` has vanishing higher cohomology on `Y`, both as
`Γ(Y, ⊤)`-modules and as `R`-modules for every morphism `Y ⟶ Spec R`. -/
def PushforwardInjectiveAcyclicStatement : Prop :=
  ∀ (X Y : Scheme.{u}) (h : X ⟶ Y) (J : X.Modules), Injective J →
    ∀ n : ℕ,
      IsZero ((DerivedSections.cohomology Y (n + 1)).obj
        ((Scheme.Modules.pushforward h).obj J)) ∧
      ∀ (R : CommRingCat.{u}) (g : Y ⟶ Spec R),
        IsZero ((DerivedSections.relativeCohomology g (n + 1)).obj
          ((Scheme.Modules.pushforward h).obj J))

end Langlands.AlgebraicGeometry.Modules

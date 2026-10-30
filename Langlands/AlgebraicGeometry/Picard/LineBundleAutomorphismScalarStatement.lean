import Langlands.AlgebraicGeometry.ModuleLinear
import Langlands.AlgebraicGeometry.Picard.LineBundle

/-! # Automorphisms of locally free rank-one sheaves are unique global units -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- For every scheme `X` and every module sheaf `M` on `X` that is locally free of
rank one, every automorphism `e : M ≅ M` is multiplication by a global unit: there is
exactly one unit `r` of `Γ(X, ⊤)` such that `e.hom` equals the sheaf morphism
`scalarHom r (𝟙 M)`, which multiplies sections over each open `U` by the restriction
of `r` to `U`. This proposition is a statement target, not a proof. -/
def LineBundleAutomorphismScalarStatement : Prop :=
  ∀ (X : Scheme.{u}) (M : X.Modules),
    IsLocallyFreeRankOne M →
      ∀ e : M ≅ M, ∃! r : Γ(X, ⊤)ˣ,
        e.hom =
          Langlands.Scheme.Modules.scalarHom (r : Γ(X, ⊤)) (𝟙 M)

end Langlands.AlgebraicGeometry.Picard

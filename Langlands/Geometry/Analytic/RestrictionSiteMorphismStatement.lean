import Langlands.Geometry.Analytic.EquivariantQuasiEtaleSite
import Mathlib.CategoryTheory.Functor.Flat

/-! # Statement: restriction of the group gives morphisms of sites `X(H)_qét → X(G)_qét` -/

universe u v z z'

open CategoryTheory

namespace Langlands.Analytic.SaturatedAtlasPresentation

/-- Statement (Berkovich 1996, §1.2): for a continuous homomorphism `f : H → G` and a `G`-space
`X`, restriction `U(G) ↦ U(H)` from `Qét(X(G))` to `Qét(X(H))` (resp. from `Ét(X(G))` to
`Ét(X(H))`) is representably flat and continuous, so the morphism `X(H) → X(G)` given by `f`
and the identity of `X` induces morphisms of sites `X(H)_qét → X(G)_qét` and
`X(H)_ét → X(G)_ét`. -/
def RestrictionSiteMorphismStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (G : Type z) [Group G] [TopologicalSpace G] (H : Type z') [Group H] [TopologicalSpace H]
    (f : H →ₜ* G) (X : GSpace.{u, v, v} K G),
    (RepresentablyFlat (EquivariantQuasiEtaleSite.res (X := X) f) ∧
        (EquivariantQuasiEtaleSite.res (X := X) f).IsContinuous (equivariantQuasiEtaleTopology X)
          (equivariantQuasiEtaleTopology ((GSpace.res f).obj X))) ∧
      (RepresentablyFlat (EquivariantEtaleSite.res (X := X) f) ∧
        (EquivariantEtaleSite.res (X := X) f).IsContinuous (equivariantEtaleTopology X)
          (equivariantEtaleTopology ((GSpace.res f).obj X)))

end Langlands.Analytic.SaturatedAtlasPresentation

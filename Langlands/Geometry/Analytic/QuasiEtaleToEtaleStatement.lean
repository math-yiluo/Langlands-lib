import Langlands.Geometry.Analytic.EquivariantQuasiEtaleSite
import Mathlib.CategoryTheory.Functor.Flat

/-! # Statement: the morphisms of sites `μ : X_qét → X_ét` and `μ_G : X(G)_qét → X(G)_ét` -/

universe u v z

open CategoryTheory

namespace Langlands.Analytic.SaturatedAtlasPresentation

/-- Statement (Berkovich 1994, §3; Berkovich 1996, §1.2): the inclusions `Ét(X) → Qét(X)` and,
for a `G`-space `X`, `Ét(X(G)) → Qét(X(G))` are representably flat and continuous, so they
define morphisms of sites `μ : X_qét → X_ét` and `μ_G : X(G)_qét → X(G)_ét`. -/
def QuasiEtaleToEtaleStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K],
    (∀ X : LocalizedCategory.{u, v, v} (K := K),
      RepresentablyFlat (EtaleSite.toQuasiEtaleSite X) ∧
        (EtaleSite.toQuasiEtaleSite X).IsContinuous (etaleTopology X) (quasiEtaleTopology X)) ∧
      ∀ (G : Type z) [Group G] [TopologicalSpace G] (X : GSpace.{u, v, v} K G),
        RepresentablyFlat (EquivariantQuasiEtaleSite.ofEquivariantEtaleSite X) ∧
          (EquivariantQuasiEtaleSite.ofEquivariantEtaleSite X).IsContinuous
            (equivariantEtaleTopology X) (equivariantQuasiEtaleTopology X)

end Langlands.Analytic.SaturatedAtlasPresentation

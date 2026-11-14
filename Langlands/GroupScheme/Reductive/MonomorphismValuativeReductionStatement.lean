import Langlands.GroupScheme.Reductive.MonomorphismClosedImmersionStatement
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-! # The noetherian/DVR reduction for reductive group monomorphisms -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

namespace ReductiveMonomorphismValuativeReduction

/-- The closed-immersion assertion over discrete valuation rings. -/
def DvrCase : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (G H : GroupScheme (Spec (CommRingCat.of R))), IsReductive G →
    IsSeparated H.X.hom → LocallyOfFinitePresentation H.X.hom → QuasiCompact H.X.hom →
    ∀ f : G ⟶ H, Mono f.hom.hom.left → IsClosedImmersion f.hom.hom.left

/-- The closed-immersion assertion over locally noetherian base schemes. -/
def LocallyNoetherianCase : Prop :=
  ∀ (S : Scheme.{u}) [IsLocallyNoetherian S] (G H : GroupScheme S), IsReductive G →
    IsSeparated H.X.hom → LocallyOfFinitePresentation H.X.hom → QuasiCompact H.X.hom →
    ∀ f : G ⟶ H, Mono f.hom.hom.left → IsClosedImmersion f.hom.hom.left

end ReductiveMonomorphismValuativeReduction

/-- The locally noetherian form of the reductive monomorphism theorem is equivalent
to its form over discrete valuation rings. This is the valuative reduction in the
first paragraph of Conrad's proof of Theorem 5.3.5, after the separate limit reduction. -/
def ReductiveMonomorphismValuativeReductionStatement : Prop :=
  ReductiveMonomorphismValuativeReduction.DvrCase.{u} ↔
    ReductiveMonomorphismValuativeReduction.LocallyNoetherianCase.{u}

end Langlands.GroupScheme

import Langlands.Geometry.Analytic.LocalActionLifts

/-! # Statement: lifts of continuous actions to compact quasi-étale spaces -/

universe u v z

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory

/-- Consequence of Berkovich's Key Lemma (1996 manuscript, §1.4): let a topological group `G`
act continuously on a Hausdorff analytic space `X`, and let `f : U ⟶ X` be quasi-étale with `U`
compact. Then the action extends to a continuous action of an open subgroup of `G` on `U` for
which `f` is equivariant, and any two such extensions agree on an open subgroup. -/
def QuasiEtaleActionLiftStatement (K : Type u) [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] : Prop :=
  ∀ (G : Type z) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (X U : LocalizedCategory.{u, v, v} (K := K)) (ρ : G →* Aut X) (f : U ⟶ X),
    T2Space (localizedSpaceFunctor.obj X) → IsContinuousAction ρ → quasiEtale f →
      IsCompactSpace U →
        Nonempty (ActionLift ρ f) ∧ ∀ a b : ActionLift ρ f, ∃ N : Subgroup G, a.AgreeOn b N

end Langlands.Analytic.SaturatedAtlasPresentation

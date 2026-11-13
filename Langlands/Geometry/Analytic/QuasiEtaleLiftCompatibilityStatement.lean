import Langlands.Geometry.Analytic.LocalActionLifts

/-! # Statement: lifts of a continuous action are compatible with morphisms over the base -/

universe u v z

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory

/-- Consequence of the uniqueness in Berkovich's Key Lemma (1994, Key Lemma 7.2, commutative
diagrams): let a topological group `G` act continuously on a Hausdorff analytic space `X`, let
`p : U ⟶ X` and `q : V ⟶ X` be quasi-étale with `U` and `V` compact, and let `f : V ⟶ U` be a
morphism over `X`. For any lifts `a` of the action to `U` and `b` to `V`, there is an open
subgroup `N` of both lift subgroups on which `f` intertwines the two actions. -/
def QuasiEtaleLiftCompatibilityStatement (K : Type u) [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] : Prop :=
  ∀ (G : Type z) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (X U V : LocalizedCategory.{u, v, v} (K := K)) (ρ : G →* Aut X) (p : U ⟶ X) (q : V ⟶ X)
    (f : V ⟶ U), f ≫ p = q →
      T2Space (localizedSpaceFunctor.obj X) → IsContinuousAction ρ → quasiEtale p →
        quasiEtale q → IsCompactSpace U → IsCompactSpace V →
          ∀ (a : ActionLift ρ p) (b : ActionLift ρ q),
            ∃ N : Subgroup G, IsOpen (N : Set G) ∧
              ∃ (ha : N ≤ a.subgroup) (hb : N ≤ b.subgroup),
                ∀ (g : G) (hg : g ∈ N),
                  (b.action ⟨g, hb hg⟩).hom ≫ f = f ≫ (a.action ⟨g, ha hg⟩).hom

end Langlands.Analytic.SaturatedAtlasPresentation

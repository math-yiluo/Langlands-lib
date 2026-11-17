import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.VectorGroupQuotient

/-! # Central series of unipotent groups with additive quotients (Milne 14.21) -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Milne 2017, Proposition 14.21: every unipotent affine algebraic group `G` over a field `k`
admits a central normal series `G = G₀ ⊇ G₁ ⊇ ⋯ ⊇ G_m = e` of closed subgroups whose quotients
`Gⱼ / Gⱼ₊₁` are isomorphic to algebraic subgroups of `𝔾ₐ`. The quotient condition is expressed by
a homomorphism `fⱼ : Gⱼ ⟶ 𝔾ₐ` with kernel `Gⱼ₊₁`, and centrality by `[G, Gⱼ] ⊆ Gⱼ₊₁` on the
points with values in every scheme over `k`. -/
def UnipotentAdditiveCentralSeriesStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom],
    IsUnipotent G →
      ∃ (m : ℕ) (H : Fin (m + 1) → GroupScheme (Spec (CommRingCat.of k)))
        (i : ∀ j, H j ⟶ G)
        (f : ∀ j : Fin m, H j.castSucc ⟶ VectorGroup.groupScheme (CommRingCat.of k) 1),
        (∀ j, IsClosedSubgroup (i j)) ∧
        SubgroupFunctor.range (i 0) = ⊤ ∧
        SubgroupFunctor.range (i (Fin.last m)) = ⊥ ∧
        (∀ j : Fin m,
          SubgroupFunctor.range (i j.succ) ≤ SubgroupFunctor.range (i j.castSucc)) ∧
        (∀ (j : Fin m) (T : Over (Spec (CommRingCat.of k))) (y : T ⟶ (H j.castSucc).X),
          y ≫ (f j).hom.hom = 1 ↔
            y ≫ (i j.castSucc).hom.hom ∈ (SubgroupFunctor.range (i j.succ)).carrier T) ∧
        (∀ (j : Fin m) (T : Over (Spec (CommRingCat.of k))) (g x : T ⟶ G.X),
          x ∈ (SubgroupFunctor.range (i j.castSucc)).carrier T →
            g * x * g⁻¹ * x⁻¹ ∈ (SubgroupFunctor.range (i j.succ)).carrier T)

end Langlands.GroupScheme

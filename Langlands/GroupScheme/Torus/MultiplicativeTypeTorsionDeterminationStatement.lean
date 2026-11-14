import Langlands.GroupScheme.Torus.RelativeMultiplicativeType
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-! # Statement: groups of multiplicative type are determined by their torsion subgroups -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open RelativeMultiplicativeType in
/-- **Torsion subgroups determine groups of multiplicative type** (SGA 3, IX, Corollaires 4.8
and 4.9, consequences of the density theorem 4.7). Let `S` be a scheme. For a group `H` and
`n > 0`, write `ₙH` for the kernel of `n · id_H`, whose `T`-points are the `x ∈ H(T)` with
`xⁿ = 1`. Subgroups are given by homomorphisms whose underlying morphism of schemes is an
immersion.
1. (4.8 a) Two homomorphisms `u, v : H ⟶ G` from an `S`-group `H` of multiplicative type to
   an arbitrary `S`-group `G` that agree on `ₙH` for every `n > 0` are equal.
2. (4.8 b) Two subgroups `H₁, H₂` of multiplicative type of an `S`-group `G` with
   `ₙH₁ = ₙH₂` for every `n > 0` are equal.
3. (4.9) A subgroup `H` of an `S`-group `G` of multiplicative type that contains `ₙG` for
   every `n > 0` is all of `G`. -/
def MultiplicativeTypeTorsionDeterminationStatement : Prop :=
  ∀ S : Scheme.{u},
    (∀ (H G : GroupScheme S), IsMultiplicativeType H → ∀ u v : H ⟶ G,
      (∀ n : ℕ, 0 < n → ∀ (T : Over S) (x : T ⟶ H.X), x ^ n = 1 →
        x ≫ u.hom.hom = x ≫ v.hom.hom) →
      u = v) ∧
    (∀ (G H₁ H₂ : GroupScheme S) (h₁ : H₁ ⟶ G) (h₂ : H₂ ⟶ G),
      IsImmersion h₁.hom.hom.left → IsImmersion h₂.hom.hom.left →
      IsMultiplicativeType H₁ → IsMultiplicativeType H₂ →
      (∀ n : ℕ, 0 < n → ∀ (T : Over S) (x : T ⟶ G.X), x ^ n = 1 →
        (x ∈ (SubgroupFunctor.range h₁).carrier T ↔ x ∈ (SubgroupFunctor.range h₂).carrier T)) →
      SubgroupFunctor.range h₁ = SubgroupFunctor.range h₂) ∧
    (∀ (G H : GroupScheme S) (h : H ⟶ G),
      IsMultiplicativeType G → IsImmersion h.hom.hom.left →
      (∀ n : ℕ, 0 < n → ∀ (T : Over S) (x : T ⟶ G.X), x ^ n = 1 →
        x ∈ (SubgroupFunctor.range h).carrier T) →
      IsIso h)

end Langlands.GroupScheme

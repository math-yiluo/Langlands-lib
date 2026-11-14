import Langlands.GroupScheme.Torus.MultiplicativeType

/-! # Statement: the torsion subgroups of a group of multiplicative type are dense -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- **Density of torsion in groups of multiplicative type** (Milne, *Algebraic Groups* (2017),
Theorems 12.32 and 12.33 and Corollary 12.34). Let `G` be a group of multiplicative type over a
field `k`, and write `G_n` for the kernel of multiplication by `n`, whose points are the points
`x` of `G` with `x ^ n = 1`.
1. A closed subscheme of `G` through which every point of every `G_n` (`n ≥ 1`) factors is all
   of `G`.
2. If `G` is smooth, the same holds using only the `G_n` with `n` invertible in `k`.
3. Two homomorphisms from `G` to an algebraic group `H` that agree on the points of every `G_n`
   (`n ≥ 1`) are equal. -/
def MultiplicativeTypeTorsionDensityStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsMultiplicativeType G →
      (∀ (Z : Scheme.{u}) (z : Z ⟶ G.X.left), IsClosedImmersion z →
        (∀ n : ℕ, 0 < n → ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X),
          x ^ n = 1 → ∃ y : T.left ⟶ Z, y ≫ z = x.left) →
        IsIso z) ∧
      (Smooth G.X.hom →
        ∀ (Z : Scheme.{u}) (z : Z ⟶ G.X.left), IsClosedImmersion z →
          (∀ n : ℕ, (n : k) ≠ 0 → ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X),
            x ^ n = 1 → ∃ y : T.left ⟶ Z, y ≫ z = x.left) →
          IsIso z) ∧
      (∀ H : GroupScheme (Spec (CommRingCat.of k)),
        LocallyOfFiniteType H.X.hom → QuasiCompact H.X.hom →
        ∀ f₁ f₂ : G ⟶ H,
          (∀ n : ℕ, 0 < n → ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X),
            x ^ n = 1 → x ≫ f₁.hom.hom = x ≫ f₂.hom.hom) →
          f₁ = f₂)

end Langlands.GroupScheme

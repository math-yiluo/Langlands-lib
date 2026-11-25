/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# Descent of separatedness along a surjective universally closed morphism

Source: Stacks Project, Morphisms, Lemma 09MQ, part (4)
(blueprint: lem-weil-pbc-surjective-universally-closed-separated).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Separatedness over a scheme descends along a surjective universally closed morphism.
Source: Stacks Project, Morphisms, Lemma 09MQ, part (4), and Schemes, the discussion
following Definition 01KK (blueprint: lem-weil-pbc-surjective-universally-closed-separated).

Proof:
1. Let `Δ_X` and `Δ_Y` be the diagonals of `p` and `q`. The induced map `f ×_S f`
   satisfies `Δ_X ≫ (f ×_S f) = f ≫ Δ_Y` by the universal property of the fibre product
   (def-pc-fibre-product).
2. The map `f ×_S f` is universally closed as a composite of base changes of `f`
   (lem-weil-pbc-universally-closed-product-map), hence is a closed map
   (def-weil-proper-morphism).
3. Since `p` is separated, `Δ_X` is a closed immersion, hence a closed map
   (def-weil-proper-morphism, def-weil-closed-immersion). Thus the image of
   `Δ_X ≫ (f ×_S f)` is closed.
4. By the commuting square and surjectivity of `f`, this image is precisely the image
   of `Δ_Y` (def-weil-surjective-morphism).
5. The diagonal `Δ_Y` is an immersion (lem-weil-pbc-diagonal-immersion). Its closed image
   makes it a closed immersion (lem-weil-pbc-immersion-closed-image-closed-immersion),
   so `q` is separated (def-weil-proper-morphism). -/
theorem isSeparated_of_surjective_universallyClosed {S X Y : Scheme.{u}}
    (p : X ⟶ S) (q : Y ⟶ S) (f : X ⟶ Y) (h : f ≫ q = p)
    [Surjective f] [UniversallyClosed f] [IsSeparated p] : IsSeparated q := by
  let F := Limits.pullback.map p p q q f f (𝟙 S)
    ((Category.comp_id p).trans h.symm) ((Category.comp_id p).trans h.symm)
  have : UniversallyClosed F :=
    MorphismProperty.pullbackMap (P := @UniversallyClosed)
      (inferInstance : UniversallyClosed f) (inferInstance : UniversallyClosed f) h.symm h.symm
  have hdiag : Limits.pullback.diagonal p ≫ F = f ≫ Limits.pullback.diagonal q := by
    apply Limits.pullback.hom_ext <;> simp [F]
  have hclosed : IsClosed (Set.range (f ≫ Limits.pullback.diagonal q)) := by
    rw [← hdiag]
    exact (Scheme.Hom.isClosedMap (Limits.pullback.diagonal p ≫ F)).isClosed_range
  have hrange : Set.range (f ≫ Limits.pullback.diagonal q) =
      Set.range (Limits.pullback.diagonal q) := by
    change Set.range ((Limits.pullback.diagonal q) ∘ f) = _
    exact (Surjective.surj (f := f)).range_comp _
  constructor
  exact IsClosedImmersion.of_isPreimmersion _ (hrange ▸ hclosed)

end AlgebraicGeometry

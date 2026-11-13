import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceValuativeExtensionExistenceStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceValuativeExistenceProof

/-!
# Valuative existence after a dominating extension

Stacks Project, Morphisms of Algebraic Spaces, Lemma 67.42.2(1) (Tag 0A3X), in the separated
form `SpaceValuativeExtensionExistenceStatement`. The trivial extension `B = A`, `L = K`
suffices, because the Library proves the existence of a lift over `A` itself
(`spaceValuativeExistence`).
-/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- **Stacks 67.42.2(1), separated case.** A quasi-compact separated universally closed
morphism of algebraic spaces admits a valuative lift after a dominating extension of
valuation rings; the identity extension already works. -/
theorem spaceValuativeExtensionExistence :
    SpaceValuativeExtensionExistenceStatement.{u} := by
  intro S X Y f hqc hf huc A _ _ _ K _ _ _ s x y hx
  obtain ⟨a, ha, hfa⟩ := spaceValuativeExistence S X Y f hqc hf huc A K s x y hx
  -- The identity of `Spec A` as a morphism of test schemes over `S`.
  let e : Over.mk (Spec.map (CommRingCat.ofHom (RingHom.id A)) ≫ s) ⟶ Over.mk s :=
    Over.homMk (Spec.map (CommRingCat.ofHom (RingHom.id A))) rfl
  refine ⟨A, inferInstance, inferInstance, inferInstance, K, inferInstance, inferInstance,
    inferInstance, RingHom.id A, inferInstance, RingHom.id K, rfl, X.pullback e a, ?_, ?_⟩
  · rw [← pullback_comp, ← ha, ← pullback_comp]
    congr 1
    ext : 1
    simp [e]
  · rw [← mapSections_naturality, hfa]

end Langlands.AlgebraicGeometry.AlgebraicSpace
